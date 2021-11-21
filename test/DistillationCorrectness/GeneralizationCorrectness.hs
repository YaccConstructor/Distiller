module DistillationCorrectness.GeneralizationCorrectness where

import Generalizer
import Driver
import LTSType
import TermType
import Test.Tasty
import Test.Tasty.HUnit
import Debug.Trace (traceShow)

qrevTerm = Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))]
t = drive (Fun "qrev") [] [("qrev", (["xs", "ys"], qrevTerm))]
qrevTerm' = Case (Free "xs") [("Nil",[],Con "Nil" []),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Con "Nil" []]))]
t' = drive (Fun "qrev") [] [("qrev", (["xs", "Nil"], qrevTerm'))]


test_checkGeneralizationCorrectness :: IO TestTree
test_checkGeneralizationCorrectness  = do {
  return $ testGroup "Tests" [testCase "let x1 = S Z in let x2 = S S Z" $ generalize t t' [] @?= t]
  }

