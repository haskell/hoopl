{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}
module Parse (parseCode) where

import Control.Monad
import qualified Data.Map as M
import Prelude hiding (id, last, succ)

import Compiler.Hoopl
import IR
import           Text.ParserCombinators.Parsec
import           Text.ParserCombinators.Parsec.Expr
import           Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as P

-- I'm stealing this parser almost directly from Daan Leijen's Parsec guide.
lexer :: P.TokenParser ()
lexer = P.makeTokenParser (haskellDef {reservedOpNames = ["+", "-", "*", "/", "=", "<"]})

-- Common lexers:
lexeme, parens, braces :: CharParser () a -> CharParser () a
lexeme = P.lexeme lexer
parens = P.parens lexer
braces = P.braces lexer

commaSep :: CharParser () a -> CharParser () [a]
commaSep   = P.commaSep   lexer

reserved :: String -> CharParser () ()
reserved = P.reserved lexer

ign :: GenParser Char st a -> GenParser Char st ()
ign p = p >> return ()

char' :: Char -> GenParser Char st ()
char' c = ign $ char c

identifier :: CharParser () String
identifier = P.identifier lexer

natural :: CharParser () Integer
natural = P.natural    lexer

reservedOp :: String -> CharParser () ()
reservedOp = P.reservedOp lexer

whitespace :: CharParser () ()
whitespace = P.whiteSpace lexer

-- Expressions:
expr :: Parser Exp
expr = buildExpressionParser table factor
    <?> "expression"
  where
    table = [[op "*"  (Binop Mul) AssocLeft, op "/"  (Binop Div) AssocLeft], 
             [op "+"  (Binop Add) AssocLeft, op "-"  (Binop Sub) AssocLeft],
             [op "="  (Binop Eq)  AssocLeft, op "/=" (Binop Ne)  AssocLeft,
              op ">"  (Binop Gt)  AssocLeft, op "<"  (Binop Lt)  AssocLeft,
              op ">=" (Binop Gte) AssocLeft, op "<=" (Binop Lte) AssocLeft]]
    op o f assoc = Infix (do {reservedOp o; return f} <?> "operator") assoc
    factor =   parens expr
           <|> lit
           <|> fetchVar
           <|> load
           <?> "simple expression"

bool :: Parser Bool
bool =  (try $ lexeme (string "True")  >> return True)
    <|> (try $ lexeme (string "False") >> return False)

lit :: Parser Exp
lit =  (natural >>= (return . Lit . Int))
   <|> (bool    >>= (return . Lit . Bool))
   <|> (bool    >>= (return . Lit . Bool))
   <?> "lit"
      
loc :: Char -> Parser x -> Parser x
loc s addr = try (lexeme (do { char' s
                             ; char' '['
                             ; a <- addr
                             ; char' ']'
                             ; return a
                             }))
          <?> "loc"

var :: Parser String
var  = identifier
    <?> "var"

mem :: Parser Exp -- address
mem  =  loc 'm' expr
    <?> "mem"

fetchVar, load :: Parser Exp
fetchVar = var >>= return . Var
load     = mem >>= return . Load


-- Statements:
type IdLabelMap = M.Map String Label
getLbl :: String -> IdLabelMap -> FuelMonad (IdLabelMap, Label)
getLbl id lmap =
  do { case M.lookup id lmap of
         Just l -> return (lmap, l)
         Nothing  -> freshLabel >>= \l ->
                     return (M.insert id l lmap, l)
     }

labl :: Parser (IdLabelMap -> FuelMonad (IdLabelMap, Label, Insn C O))
labl = lexeme (do { id <- identifier
                  ; char' ':'
                  ; return $ \lmap -> do { (m, l) <- getLbl id lmap
                                         ; return (m, l, Label l)
                                         }
                  })
  <?> "label"

mid :: Parser (Insn O O)
mid =   asst
    <|> store
    <?> "assignment or store"

asst :: Parser (Insn O O)
asst = do { v <- lexeme var
          ; lexeme (char' '=')
          ; e <- expr
          ; return $ Assign v e
          }
    <?> "asst"

store :: Parser (Insn O O)
store = do { addr <- lexeme mem
           ; lexeme (char' '=')
           ; e <- expr
           ; return $ Store addr e
           }
     <?> "store"

type LastParse = Parser (IdLabelMap -> FuelMonad (IdLabelMap, Insn O C))
last :: LastParse
last =  branch
    <|> cond
    <|> call
    <|> ret
    <?> "control-transfer"


goto :: Parser String
goto = do { lexeme (reserved "goto")
          ; identifier
          }
    <?> "goto"

branch :: LastParse
branch =
    do { l <- goto
       ; return $ \lmap -> do { (m, lbl) <- getLbl l lmap
                              ; return (m, Branch lbl)
                              } 
       }
 <?> "branch"

cond, call, ret :: LastParse
cond =
  do { lexeme (reserved "if")
     ; cnd <- expr
     ; lexeme (reserved "then")
     ; thn <- goto
     ; lexeme (reserved "else")
     ; els <- goto
     ; return $ \lmap -> do { (m',  tlbl) <- getLbl thn lmap
                            ; (m'', flbl) <- getLbl els m'
                            ; return (m'', Cond cnd tlbl flbl)
                            }
     }
 <?> "cond"

call =
  do { results <- tuple var
     ; lexeme (char' '=')
     ; f <- identifier
     ; params  <- tuple expr
     ; succ <- goto
     ; return $ \lmap -> do { (m',  slbl) <- getLbl succ lmap
                            ; return (m', Call results f params slbl)
                            }
     }
 <?> "call"

ret =
  do { lexeme (reserved "ret")
     ; results <- tuple expr
     ; return $ \lmap -> return (lmap, Return results)
     }
 <?> "ret"

block :: Parser (IdLabelMap -> FuelMonad (IdLabelMap, Label, Graph Insn C C))
block =
  do { f   <- lexeme labl
     ; ms  <- many $ try mid
     ; l   <- lexeme last
     ; return $ \lmap -> do { (lmap1, lbl, first) <- f lmap
                            ; (lmap2, lst)        <- l lmap1
                            ; g <- foldl (<*>) (mkFirst first) (map mkMiddle ms)
                                              <*> mkLast lst
                            ; return (lmap2, lbl, g)
                            }
     }
 <?> "Expected basic block; maybe you forgot a label following a control-transfer?"

tuple :: Parser a -> Parser [a]
tuple = parens . commaSep

infix 3 <**>
(<**>) :: AGraph n e C -> AGraph n C x -> AGraph n e x
(<**>) = gCatClosed

procBody :: Parser (IdLabelMap -> FuelMonad (IdLabelMap, Label, Graph Insn C C))
procBody = do { b  <- block
              ; bs <- many block
              ; return $ \lmap ->
                   do { (lmap1, lbl, b') <- b lmap
                      ; (lmap2, bs') <-
                          foldM threadMap (lmap1, emptyClosedAGraph) $ bs
                      ; g <- return b' <**> bs'
                      ; return (lmap2, lbl, g)
                      }
              }
        <?> "proc body"
  where
    threadMap :: (IdLabelMap, AGraph Insn C C)
              -> (IdLabelMap -> FuelMonad (IdLabelMap, Label, Graph Insn C C))
              -> FuelMonad (IdLabelMap, AGraph Insn C C)
    threadMap (lmap, bdy) f = do (lmap', _, b) <- f lmap
                                 return (lmap', return b <**> bdy)

proc :: Parser (FuelMonad Proc)
proc = do { whitespace
          ; f      <- identifier
          ; params <- tuple  var
          ; bdy    <- braces procBody
          ; return $ do { (_, lbl, code) <- bdy M.empty
                        ; return $ Proc { name = f, args = params
                                        , body = bodyOf code, entry = lbl }
                        }
          }
    <?> "proc"
  where bodyOf :: Graph a C C -> Body a
        bodyOf (GMany NothingO b NothingO) = b

parseCode :: String -> String -> Either ParseError (FuelMonad [Proc])
parseCode file inp =
  case parse (many proc) file inp of
    Right ps -> Right $ sequence ps
    Left  e  -> Left e
