module DistillationCorrectness.ResidualizerCorrectness where

import Test.Tasty.Providers (TestTree)
import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TermType
import HelperTypes (renaming)  
import LTSType 
import Residualizer
  
test_checkResidualizer_case :: IO TestTree
test_checkResidualizer_case = let 
    lts = LTS (LTSTransitions (Free "not important") 
        [(Case', doLTS1Tr (Free "xs") (X' "xs") doLTS0Tr)
        ,(CaseBranch' "Cons" ["x'","xs'"], doLTS1Tr (Free "xs'") (X' "xs'") doLTS0Tr {--doLTSManyTr (Con "Cons" [Free "x'", Free "xs'"]) 
            [(Con' "Cons", doLTS0Tr)
            ,(ConArg' "x'", doLTS1Tr (Free "x'") (X' "x'") doLTS0Tr)
            ,(ConArg' "xs'", doLTS1Tr (Free "x'") (X' "x'") doLTS0Tr)]-})
        ,(CaseBranch' "Nil" [], doLTS1Tr (Con "Nil" []) (Con' "Nil") doLTS0Tr)])
    expected = Case (Free "xs") 
        [("Cons", ["x'", "xs'"], Free "xs'")
        ,("Nil", [], Con "Nil" [])]    
    in return $ testGroup "Residualizer" [testCase "case xs of Cons(x',xs') => xs'; Nil => Nil" $ residualize lts @?= expected] 

