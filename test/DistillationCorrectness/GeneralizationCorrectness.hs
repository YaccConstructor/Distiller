module DistillationCorrectness.GeneralizationCorrectness where

import Generalizer
import Driver
import LTSType
import TermType
import Test.Tasty
import Test.Tasty.HUnit

qrevTerm = Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))]
t = drive (Fun "qrev") [] [("qrev", (["xs", "ys"], qrevTerm))]
qrevTerm' = Case (Free "xs") [("Nil",[],Con "Nil" []),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Con "Nil" []]))]
t' = drive (Fun "qrev") [] [("qrev", (["xs", "Nil"], qrevTerm'))]


test_checkGeneralizationCorrectness :: IO TestTree
test_checkGeneralizationCorrectness  = let
  expectedLts = LTS (LTSTransitions (Fun "qrev") 
    [(Let', LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))]) [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "x") [(X' "Free \"x\"",Leaf)])),(CaseBranch' "Cons" ["x","xs"],LTS (LTSTransitions (Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"])) [(Apply0',LTS (LTSTransitions (Apply (Fun "qrev") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])),(Apply1',LTS (LTSTransitions (Con "Cons" [Free "x",Free "ys"]) [(Con' "Cons",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x") [(X' "x",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Free "x") [(X' "Free \"x\"",Leaf)]))]))]))]))])),
    (X' "x", LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))])
  in return $ testGroup "Tests" [testCase "let x1 = S Z in let x2 = S S Z" $ generalize t t' [] @?= expectedLts]
 

