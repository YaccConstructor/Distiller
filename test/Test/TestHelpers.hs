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

substituteAll :: Foldable t => Term -> t (String, Term) -> Term
substituteAll =
    foldl (\ term (name, subst_term) -> subst subst_term (abstract term name)) 

getEvalResults :: (Num a1, Foldable t1, Num a2, Foldable t3, Foldable t2) =>
                  t2 (String, Term)
                  -> (Term, [(String, (t3 String, Term))])
                  -> (Term, [(String, (t1 String, Term))])
                  -> ((Term, Int, a2), (Term, Int, a1))
getEvalResults substitutions (origMainTerm, origTerms) (distilledMainTerm, distilledTerms) =         
    let origResults = Term.eval (substituteAll origMainTerm substitutions) EmptyCtx origTerms 0 0            
        distilledResults = Term.eval (substituteAll distilledMainTerm substitutions)  EmptyCtx distilledTerms 0 0
    in (origResults, distilledResults)    


