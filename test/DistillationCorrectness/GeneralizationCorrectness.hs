module DistillationCorrectness.GeneralizationCorrectness where

import Generalizer
import Driver
import LTSType
import TermType
import Test.Tasty
import Test.Tasty.HUnit
import Debug.Trace (trace)

qrevTerm = Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))]
qrevLts = drive (Fun "qrev") [] [("qrev", (["xs", "ys"], qrevTerm))]
qrevTerm' = Case (Free "xs") [("Nil",[],Con "Nil" []),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Con "Nil" []]))]
qrevLts' = drive (Fun "qrev") [] [("qrev", (["xs", "Nil"], qrevTerm'))]

test_checkGeneralizationCorrectness :: IO TestTree
test_checkGeneralizationCorrectness  = let
  expectedLts = LTS (LTSTransitions (Fun "qrev") 
    [(Let', LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))]) [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "x") [(X' "x",Leaf)])),(CaseBranch' "Cons" ["x","xs"],LTS (LTSTransitions (Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"])) [(Apply0',LTS (LTSTransitions (Apply (Fun "qrev") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])),(Apply1',LTS (LTSTransitions (Con "Cons" [Free "x",Free "ys"]) [(Con' "Cons",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x") [(X' "x",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Free "x") [(X' "x",Leaf)]))]))]))]))])),
    (X' "x", LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))])
  in return $ testGroup "Tests" [testCase "qrev xs [] & qrev xs ys" $ generalize qrevLts qrevLts' [] @?= expectedLts]

swapQrevTerm = Case (Free "ys") [("Nil",[],Free "xs"),("Cons",["y","ys"],Apply (Apply (Fun "qrev") (Free "ys")) (Con "Cons" [Free "y",Free "xs"]))]
swapQrevLts = drive (Fun "qrev") [] [("qrev", (["xs", "ys"], swapQrevTerm))]
swapQrevTerm' = Case (Free "ys") [("Nil",[],Con "Nil" []),("Cons",["y","ys"],Apply (Apply (Fun "qrev") (Free "ys")) (Con "Cons" [Free "y",Con "Nil" []]))]
swapQrevLts' = drive (Fun "qrev") [] [("qrev", (["Nil", "ys"], swapQrevTerm'))]

test_checkGeneralizationCorrectness_qrev_swap :: IO TestTree
test_checkGeneralizationCorrectness_qrev_swap = let
  expectedLts = LTS (LTSTransitions (Fun "qrev") [(Let',LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",LTS (LTSTransitions (Case (Free "ys") [("Nil",[],Free "xs"),("Cons",["y","ys"],Apply (Apply (Fun "qrev") (Free "ys")) (Con "Cons" [Free "y",Free "xs"]))]) [(Case',LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "x") [(X' "x",Leaf)])),(CaseBranch' "Cons" ["y","ys"],LTS (LTSTransitions (Apply (Apply (Fun "qrev") (Free "ys")) (Con "Cons" [Free "y",Free "xs"])) [(Apply0',LTS (LTSTransitions (Apply (Fun "qrev") (Free "ys")) [(Apply0',LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",Leaf)])),(Apply1',LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))])),(Apply1',LTS (LTSTransitions (Con "Cons" [Free "y",Free "xs"]) [(Con' "Cons",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "y") [(X' "y",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Free "x") [(X' "x",Leaf)]))]))]))]))])),(X' "x",LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])
  in return $ testGroup "Tests" [testCase "qrev [] ys & qrev xs ys" $ generalize swapQrevLts swapQrevLts' [] @?= expectedLts]


appendTerm' = Case (Free "xs'")
    [("Nil",[],Con "Con" [Free "x'", Free "xs'"])
    ,("Cons",["x''","xs''"],Con "Cons" [Free "x''",Apply (Apply (Fun "append") (Free "xs''")) (Con "Con" [Free "x'", Free "xs'"])])]
appendLts' = drive (Fun "append") [] [("append", (["xs'", "Con(x',xs')"], appendTerm'))]
appendTerm = Case (Free "xs") [("Nil",[],Free "xs"),("Cons",["x'","xs'"],Con "Cons" [Free "x'",Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")])]
appendLts = drive (Fun "append") [] [("append", (["xs", "xs"], appendTerm))]

test_checkGeneralizationCorrectness_append :: IO TestTree
test_checkGeneralizationCorrectness_append = let
    expectedLts = LTS (LTSTransitions (Fun "append") [(Let',LTS (LTSTransitions (Fun "append") [(Unfold' "append",LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Free "xs"),("Cons",["x'","xs'"],Con "Cons" [Free "x'",Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")])]) [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "x") [(X' "x",Leaf)])),(CaseBranch' "Cons" ["x'","xs'"],LTS (LTSTransitions (Con "Cons" [Free "x'",Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")]) [(Con' "Cons",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x'") [(X' "x'",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")) [(Apply0',LTS (LTSTransitions (Apply (Fun "append") (Free "xs'")) [(Apply0',LTS (LTSTransitions (Fun "append") [(Unfold' "append",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs'") [(X' "xs'",Leaf)]))])),(Apply1',LTS (LTSTransitions (Free "x") [(X' "x",Leaf)]))]))]))]))])),(X' "x",LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])
    in do return $ testGroup "Tests" [testCase "append xs xs & append xs Cons(x,xs)" $ generalize appendLts appendLts' [] @?= expectedLts]

neil3Term = Case (Apply (Fun "f") (Free "xs'"))    
                     [("True", [],Apply (Fun "f") (Free "xs'"))
                     ,("False", [], Con "False" [])]
fDef = Case (Free "xs") 
    [("Nil",[], Con "True" [])
    ,("Cons",["x","xs"],Case (Apply (Fun "f") (Free "xs")) [("True", [], Apply (Fun "f") (Free "xs")), ("False",[], Con "False" [])])
    ]
neil3Lts = drive neil3Term [] [("f", (["xs"], fDef))]
neil3Term' = Case (Case (Apply (Fun "f") (Free "xs''"))    
                                        [("True", [],Apply (Fun "f") (Free "xs''"))
                                        ,("False", [], Con "False" [])])    
                     [("True", [],Apply (Fun "f") (Con "Con" [Free "x'", Free "xs''"]))
                     ,("False", [], Con "False" [])]
neil3Lts' = drive neil3Term' [] [("f", ([], fDef))]                     


test_checkGeneralizationCorrectness_neil3 :: IO TestTree
test_checkGeneralizationCorrectness_neil3 = let 
    expectedLts = doLTS0Tr
    in do return $ testGroup "Tests" [testCase "append xs xs & append xs Cons(x,xs)" $ generalize neil3Lts neil3Lts' [] @?= expectedLts]


