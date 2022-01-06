module DistillationCorrectness.ResidualizerCorrectness where

import Test.Tasty.Providers (TestTree)
import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TermType
import HelperTypes (renaming)
import LTSType
import Residualizer
import Driver (drive)
import InputData

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

test_checkResidualizer_fun_neil3 :: IO TestTree
test_checkResidualizer_fun_neil3 = let
    lts = drive (Apply (Fun "f") (Free "xs")) [] [("f", (["xs"], neil3Def))]
    expected = Apply
        (Lambda "xs" (Case (Free "xs")
            [("Nil",[],Con "True" [])
            ,("Cons",["x","xs"],Case (Apply (Fun "f") (Free "xs")) [("True",[],Apply (Fun "f") (Free "xs")),("False",[],Con "False" [])])
            ]))
        (Free "xs")
    in return $ testGroup "Residualizer" [testCase "neil3 xs" $ residualize lts @?= expected]

test_checkResidualizer_fun_qrev :: IO TestTree
test_checkResidualizer_fun_qrev = let
    lts = drive (Fun "qrev") [] [("qrev", (["xs", "ys"], qrevTerm))]
    expected =  Lambda "x" (Lambda "ys" (Lambda "xs" (Case (Free "xs")
        [("Nil",[],Free "ys")
        ,("Cons",["x","xs"],Apply (Apply (Fun "f") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))
        ])))
    in return $ testGroup "Residualizer" [testCase "qrev xs" $ residualize lts @?= expected]

test_checkResidualizer_fun_qrev_with_accum :: IO TestTree
test_checkResidualizer_fun_qrev_with_accum = let
    lts1 = drive (Fun "qrev") [] [("qrev", (["xs", "ys"], qrevTerm))]
    lts2 = drive (Fun "qrev") [] [("qrev", (["xs", "ys"], qrevTerm'))]
    lts' = doLTSManyTr (Apply (Apply (Fun "qrev") (Free "xs")) (Apply (Apply (Fun "qrev") (Free "xs")) (Con "Nil" [])))
        [(Apply0', doLTSManyTr (Apply (Fun "qrev") (Free "xs"))
            [(Apply0', lts1)
            ,(Apply1', doLTS1Tr (Free "xs") (X' "xs") doLTS0Tr)])
        ,(Apply1', doLTSManyTr (Apply (Apply (Fun "qrev") (Free "xs")) (Free "xs"))
            [(Apply0', doLTSManyTr (Apply (Fun "qrev") (Free "xs"))
                [(Apply0', lts2)
                ,(Apply1', doLTS1Tr (Free "xs") (X' "xs") doLTS0Tr)])
            ,(Apply1', doLTS1Tr (Con "Nil" []) (Con' "Nil") doLTS0Tr)])]

    expected = Apply 
        (Apply (Lambda "x" (Lambda "ys" (Lambda "xs" (Case (Free "xs") 
            [("Nil",[],Free "ys")
            ,("Cons",["x","xs"],Apply (Apply (Fun "f") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))])))) (Free "xs")) 
        (Apply (Apply (Lambda "x" (Lambda "xs" (Case (Free "xs") 
            [("Nil",[],Con "Nil" [])
            ,("Cons",["x","xs"],Apply (Apply (Fun "f") (Free "xs")) (Con "Cons" [Free "x",Con "Nil" []]))]))) (Free "xs")) (Con "Nil" []))
    in return $ testGroup "Residualizer" [testCase "qrev xs" $ residualize lts' @?= expected]