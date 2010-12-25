module Main (main) where

import Test

-- Hardcoding test locations for now
tests = map (\t -> "tests" ++ "/" ++ t)
            (["test1", "test2", "test3", "test4"] ++
             ["if-test", "if-test2", "if-test3", "if-test4"])

main :: IO ()
main = do mapM (\x -> putStrLn ("Test:" ++ x) >> parseTest x >> optTest x) tests
          return ()
