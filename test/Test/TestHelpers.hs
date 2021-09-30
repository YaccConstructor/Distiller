module Test.TestHelpers where

import Helpers
import Test.Tasty
import Test.Tasty.HUnit
import Data.Maybe (fromJust, isJust)
import Term
import Trans (dist)

defaultTimeout :: Integer
defaultTimeout = 2 * 1000000 --timeout in nanoseconds: 1 sec = 10^6 ns 

_10sec :: Integer
_10sec = 10 * 1000000

_1min :: Integer
_1min = 60 * 1000000

timeOutTest :: Integer -> TestName -> Assertion -> TestTree
timeOutTest timeout testName assertion =
  localOption (mkTimeout timeout) $ testCase testName assertion

load :: String -> String -> IO (Maybe (Term, [(String, ([String], Term))]))
load root imports = loadProg [root] [] [] $ Just imports

loadFileToTerm file = do
    str <- readFile file
    return $ parseTerm str


