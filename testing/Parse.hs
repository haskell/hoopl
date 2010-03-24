{-# OPTIONS_GHC -Wall #-}
module Parse (parseCode) where

import Prelude hiding (succ)

import Hoopl
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
loc s addr = try (lexeme (do { char s
                             ; char '['
                             ; a <- addr
                             ; char ']'
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
-- THE FOLLOWING IS EVIL, AND WE SHOULD NOT EXPORT THE BLOCKID TYPE.
-- USE THE MONAD TO MAP LABELS TO BLOCKIDS, AND DO THIS PROPERLY...
lbl :: Parser (Node C O)
lbl = lexeme (do { l <- natural
                 ; char ':'
                 ; return $ Label $ fromInteger l
                 })
    <?> "label"

mid :: Parser (Node O O)
mid =   asst
    <|> store
    <?> "assignment or store"

asst :: Parser (Node O O)
asst = do { v <- lexeme var
          ; lexeme (char '=')
          ; e <- expr
          ; return $ Assign v e
          }
    <?> "asst"

store :: Parser (Node O O)
store = do { addr <- lexeme mem
           ; lexeme (char '=')
           ; e <- expr
           ; return $ Store addr e
           }
     <?> "store"

lst :: Parser (Node O C)
lst =   branch
    <|> cond
    <|> call
    <|> ret
    <?> "control-transfer"


goto :: Parser Int
goto = do { lexeme (string "goto")
          ; l <- natural
          ; return $ fromInteger l
          }
    <?> "goto"

branch :: Parser (Node O C)
branch = do { l <- goto
            ; return $ Branch l -- Integer is bogus...
            }
      <?> "branch"

cond, call, ret :: Parser (Node O C)
cond = do { lexeme (string "if")
          ; cnd <- expr
          ; lexeme (string "then")
          ; thn <- goto
          ; lexeme (string "else")
          ; els <- goto
          ; return $ Cond cnd thn els
          }
    <?> "cond"

call = do { results <- tuple var
          ; lexeme (char '=')
          ; f <- identifier
          ; params  <- tuple expr
          ; succ <- goto
          ; return $ Call results f params succ
          }
    <?> "call"

ret  = do { lexeme (string "ret")
          ; results <- tuple expr
          ; return $ Return results
          }
    <?> "ret"

block :: Parser (Block Node C C)
block = do { f  <- lexeme lbl
           ; ms <- many $ try mid
           ; l  <- lexeme lst
           ; return $ BCat (foldl BCat (BUnit f) $ map BUnit ms) (BUnit l)
           }
     <?> "Expected basic block; maybe you forgot a label following a control-transfer?"

tuple :: Parser a -> Parser [a]
tuple = parens . commaSep

procBody :: Parser (BlockId, Graph Node C C)
procBody = do { b  <- block
              ; bs <- many block
              ; return $ (blockId b, GMany { g_entry = ClosedLink, g_blocks = b : bs, g_exit = ClosedLink})
              }
        <?> "proc body"

proc :: Parser Proc
proc = do { whitespace
          ; f           <- identifier
          ; params      <- tuple  var
          ; (eid, code) <- braces procBody
          ; return $ Proc { name = f, args = params, body = code, entry = eid }
          }
    <?> "proc"

parseCode :: String -> String -> Either ParseError [Proc]
parseCode file inp = parse (many proc) file inp
