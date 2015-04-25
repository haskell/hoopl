module Main (main) where

import Test
import System.IO

-- Hardcoding test locations for now
tests = map (\t -> "testing" ++ "/" ++ "tests" ++ "/" ++ t)
        (["test1", "test2", "test3", "test4"] ++
             ["if-test", "if-test2", "if-test3", "if-test4"])
        
test_expected_results = map (\t -> "testing" ++ "/" ++ "tests" ++ "/" ++ t)
                        (["test1.expected", "test2.expected", "test3.expected", "test4.expected"] ++
                         ["if-test.expected", "if-test2.expected", "if-test3.expected", "if-test4.expected"])
        

main :: IO ()
main = do hSetBuffering stdout NoBuffering
          hSetBuffering stderr NoBuffering
          mapM (\(x, ex) -> putStrLn ("Test:" ++ x) >> parseTest x >> optTest x ex) (zip tests test_expected_results)
          return ()
