module Main (main) where

import Test

-- Hardcoding test locations for now
tests = map (\t -> "tests" ++ "/" ++ t)
            ["if-test2", "if-test3", "if-test4"]
            -- ["test1", "test2", "test3", "test4", "if-test"]

main :: IO ()
-- main = do mapM evalTest tests
main = do mapM optTest tests
          return ()
