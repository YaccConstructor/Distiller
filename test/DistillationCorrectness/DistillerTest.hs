module DistillationCorrectness.DistillerTest where

import Test.Tasty.Providers (TestTree)
import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TermType
import Distiller

test_and :: IO TestTree
test_and = let
    funTerm = Apply (Apply (Fun "and") (Free "x")) (Con "False" [])
    funDef = [("and",(["x","y"],Case (Free "x") [("True",[],(Free "y")),("False",[],Con "False" [])]))]
    result = Lambda "y" (Lambda "x" (Case (Free "x") [("True",[],Con "False" []),("False",[],Con "False" [])]))
    in return $ testGroup "Distiller" [testCase "Distiller: and x False" $ distillProg (funTerm, funDef) @?= result]

test_not :: IO TestTree
test_not = let
    funTerm = Apply (Fun "not") (Free "x")
    funDef = [("not",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))]
    result = Lambda "x" (Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])])
    in return $ testGroup "Distiller" [testCase "Distiller: not x" $ distillProg (funTerm, funDef) @?= result]

test_or :: IO TestTree
test_or = let
    funTerm = Apply (Apply (Fun "or") (Free "x")) (Free "y")
    funDef = [("or",(["x","y"],Case (Free "x") [("True",[],Con "True" []),("False",[],Free "y")]))]
    result = Lambda "y" (Lambda "x" (Case (Free "x") [("True",[],Con "True" []),("False",[],Free "y")]))
    in return $ testGroup "Distiller" [testCase "Distiller: or x y" $ distillProg (funTerm, funDef) @?= result]

test_iff :: IO TestTree
test_iff = let
    funTerm = Apply (Apply (Fun "iff") (Con "True" [])) (Free "x")
    funDef = [("iff",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Apply (Fun "not") (Free "y"))]))
             ,("not",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))]
    result = Lambda "y" (Lambda "x" (Free "x"))
    in return $ testGroup "Distiller" [testCase "Distiller: iff True x" $ distillProg (funTerm, funDef) @?= result]

test_eqBool :: IO TestTree
test_eqBool = let
    funTerm = Apply (Apply (Fun "eqBool") (Free "x")) (Con "False" [])
    funDef = [("eqBool",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Apply (Fun "not") (Free "y"))]))
             ,("not",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))]
    result = Lambda "y" (Lambda "x" (Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))
    in return $ testGroup "Distiller" [testCase "Distiller: iff True x" $ distillProg (funTerm, funDef) @?= result]

test_implies :: IO TestTree
test_implies = let
    funTerm = Apply (Apply (Fun "implies") (Free "x")) (Con "True" [])
    funDef = [("implies",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Con "True" [])]))]
    result = Lambda "y" (Lambda "x" (Case (Free "x") [("True",[],Con "True" []),("False",[],Con "True" [])]))
    in return $ testGroup "Distiller" [testCase "Distiller: iff True x" $ distillProg (funTerm, funDef) @?= result]
    
test_append :: IO TestTree
test_append = let 
    funTerm = Apply (Apply (Fun "append") (Free "xs")) (Free "ys")
    funDef = [("append",(["xs","ys"],Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Con "Cons" [Free "x",Apply (Apply (Fun "append") (Free "xs")) (Free "ys")])]))]
    result = Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Con "Cons" [Free "x",Apply (Apply (Fun "f") (Free "xs")) (Free "ys")])]
    in return $ testGroup "Distiller" [testCase "Distiller: append xs ys" $ distillProg (funTerm, funDef) @?= result]           