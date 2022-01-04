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
        ,(CaseBranch' "Cons" ["x'","xs'"], doLTS1Tr (Free "xs'") (X' "xs'") doLTS0Tr)
        ,(CaseBranch' "Nil" [], doLTS1Tr (Con "Nil" []) (Con' "Nil") doLTS0Tr)])
    expected = Case (Free "xs")
        [("Cons", ["x'", "xs'"], Free "xs'")
        ,("Nil", [], Con "Nil" [])]
    in return $ testGroup "Residualizer" [testCase "case xs of Cons(x',xs') => xs'; Nil => Nil" $ residualize lts @?= expected]

test_checkResidualizer_let :: IO TestTree
test_checkResidualizer_let = let
    lts = LTS (LTSTransitions (Free "not important")
        [(Let', doLTSManyTr (Apply (Apply (Fun "f") (Free "x1")) (Free "x2"))
            [(Apply0', doLTSManyTr (Apply (Fun "f") (Free "x1"))
                [(Apply0', doLTS1Tr (Fun "f") (Unfold' "f") (doLTSManyTr (Con "Nil" []) [(Con' "Nil", doLTS0Tr)]))
                ,(Apply1', doLTS1Tr (Free "x1") (X' "x1") doLTS0Tr)])
            ,(Apply1', doLTS1Tr (Free "x2") (X' "x2") doLTS0Tr)])
        ,(X' "x1", doLTSManyTr (Con "Cons" [Free "x'", Free "xs'"])
                                              [(Con' "Cons", doLTS0Tr)
                                              ,(ConArg' "#1", doLTS1Tr (Free "x'") (X' "x'") doLTS0Tr)
                                              ,(ConArg' "#2", doLTS1Tr (Free "x'") (X' "x'") doLTS0Tr)])
        ,(X' "x2", doLTSManyTr (Con "Nil" []) [(Con' "Nil", doLTS0Tr)])])
    expected = Let "x1" (Con "Cons" [Free "x'",Free "x'"]) (Let "x2" (Con "Nil" []) (Apply (Apply (Con "Nil" []) (Free "x1")) (Free "x2")))
    in return $ testGroup "Residualizer" [testCase "let x1 = Cons(x',xs') in x2 = Nil in f x1 x2" $ residualize lts @?= expected]