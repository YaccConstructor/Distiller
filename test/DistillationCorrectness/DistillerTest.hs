{-# LANGUAGE LambdaCase #-}

module DistillationCorrectness.DistillerTest where

import Test.Tasty.Providers (TestTree)
import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TermType
import Distiller
import DistillationHelpers

_x = "x"
_y = "y"
false = Con "False" []
true = Con "True" []
freex = Free _x
freey = Free _y
xTerms = [Free "x", false, true]
yTerms = [false, true]
xyTerms = [(x, y) | x <- xTerms, y <- yTerms]

generateTestCase expectedTerms expectedFunDefs givenFunTerms results = let
     description x y = "Term = " ++ show x ++ ", distilled " ++ y
     termsTestCases = zipWith3 (\result expectedTerm givenTerm ->
             testCase (description givenTerm "term") $ result @?= expectedTerm) (map fst results) expectedTerms givenFunTerms
     funDefsTestCases = zipWith3 (\result expectedFunDef givenTerm ->
             testCase (description givenTerm "fundef") $ expectedFunDef `elem` result @?= True) (map snd results) expectedFunDefs givenFunTerms
     in testGroup "Distiller" $ termsTestCases ++ funDefsTestCases

test_and :: IO TestTree
test_and = let

    givenFunTerms = map (\(x, y) -> Apply (Apply (Fun "and") x) y) xyTerms
    givenFunDef = [("and",([_x, _y],Case freex [("True", [], Free _y),("False", [], false)]))]

    results = map (\funTerm -> distillProg (funTerm, givenFunDef)) givenFunTerms

    funDefTerm = Case (Free _x) [("True",[], Free _y),("False",[], false)]
    expectedFunDefsTerms = map (\(x, y) -> case (x, y) of
            (Con "True" [], Con "True" []) -> true
            (Free "x", _)  -> let
                term = substituteTermWithNewTerm funDefTerm (_y, y)
                in substituteTermWithNewTerm term (_x, x)
            _ -> false) xyTerms
    expectedTerms = map (\(x, y) -> case (x, y) of
                            (Con "True" [], Con "True" []) -> true
                            (Free "x", _) -> Apply (Fun "f'") freex
                            _ -> false) xyTerms
    expectedFunDefs = map (\funDef -> ("f'", (free funDef, funDef))) expectedFunDefsTerms
    in return $ generateTestCase expectedTerms expectedFunDefs givenFunTerms results

test_not :: IO TestTree
test_not = let
    givenFunTerms = map (Apply (Fun "not")) xTerms
    givenFunDef = [("not",([_x],Case freex [("True", [], false),("False", [], true)]))]
    results = map (\funTerm -> distillProg (funTerm, givenFunDef)) givenFunTerms

    funDef = Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]
    expectedFunDefsTerms = map (\case
                                  Con "True" [] -> false
                                  Con "False" [] -> true
                                  _ -> funDef) xTerms
    expectedTerms = map (\case
                           Con "True" [] -> false
                           Con "False" [] -> true
                           _ -> Apply (Fun "f'") (Free "x")) xTerms
    expectedFunDefs = map (\funDef -> ("f'", (free funDef, funDef))) expectedFunDefsTerms
    in return $ generateTestCase expectedTerms expectedFunDefs givenFunTerms results

test_or :: IO TestTree
test_or = let
    or = "or"
    funDefTerm = Case (Free _x) [("True",[], Con "True" []),("False",[], freey)]

    givenFunTerms = map (\(x, y) -> Apply (Apply (Fun or) x) y) xyTerms
    givenFunDef = [(or, ([_x, _y], Case freex [("True",[], true),("False",[], freey)]))]
    results = map (\funTerm -> distillProg (funTerm, givenFunDef)) givenFunTerms

    expectedFunDefsTerms = map (\(x, y) -> case (x, y) of
                (Con "True" [], _) -> true
                (Con "False" [], Con "True" []) -> true
                (Con "False" [], Con "False" []) -> false
                _  -> let
                    term = substituteTermWithNewTerm funDefTerm (_y, y)
                    in substituteTermWithNewTerm term (_x, x)) xyTerms
    expectedTerms = map (\(x, y) -> case (x, y) of
                                (Con "True" [], _) -> true
                                (Con "False" [], Con "True" []) -> true
                                (Con "False" [], Con "False" []) -> false
                                _ -> Apply (Fun "f'") freex) xyTerms
    expectedFunDefs = map (\funDef -> ("f'", (free funDef, funDef))) expectedFunDefsTerms
    in return $ generateTestCase expectedTerms expectedFunDefs givenFunTerms results

test_iff :: IO TestTree
test_iff = let
    funTerm = Apply (Apply (Fun "iff") (Free "x")) (Free "y")
    funDef = [("iff",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Apply (Fun "not") (Free "y"))]))
             ,("not",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))]
    result = distillProg (funTerm, funDef)
    resultTerm = Apply (Apply (Fun "f''") (Free "x")) (Free "y")
    expectedFunDef = ("f''",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Case (Free "y") [("True",[],Con "False" []),("False",[],Con "True" [])])]))
    in return $ testGroup "Distiller" [testCase "Distiller: iff x y, term" $ resultTerm @?= fst result
                                      ,testCase "Distiller: iff x y, fundef" $ expectedFunDef `elem` snd result @?= True]

test_eqBool :: IO TestTree
test_eqBool = let
    funTerm = Apply (Apply (Fun "eqBool") (Free "x")) (Con "False" [])
    funDef = [("eqBool",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Apply (Fun "not") (Free "y"))]))
             ,("not",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))]
    result = distillProg (funTerm, funDef)
    expectedTerm = Apply (Fun "f''") (Free "x")
    expectedFunDef = ("f''",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))
    in return $ testGroup "Distiller" [testCase "Distiller: eqBool x False, term " $ fst result @?= expectedTerm
                                      ,testCase "Distiller: eqBool x False, fundef " $ expectedFunDef `elem` snd result @?= True]

test_implies :: IO TestTree
test_implies = let
    funTerm = Apply (Apply (Fun "implies") (Free "x")) (Con "True" [])
    funDef = [("implies",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Con "True" [])]))]
    result = distillProg (funTerm, funDef)
    expectedTerm = Apply (Fun "f'") (Free "x")
    expectedFunDef = ("f'",(["x"],Case (Free "x") [("True",[],Con "True" []),("False",[],Con "True" [])]))
    in return $ testGroup "Distiller" [testCase "Distiller: implies x True" $ fst result @?= expectedTerm
                                      ,testCase "Distiller: eqBool x False, fundef " $ expectedFunDef `elem` snd result @?= True]

test_f :: IO TestTree
test_f = let
    funTerm = Apply (Fun "f") (Free "x")
    funDef = [("f",(["x"],Apply (Fun "f") (Free "x")))]
    result = (Apply (Fun "f") (Free "x"), funDef)  
    in return $ testGroup "Distiller" [testCase "Distiller: f x = f x" $ distillProg (funTerm, funDef) @?= result]

test_f_g :: IO TestTree
test_f_g = let
    funTerm = Apply (Fun "d") (Free   "x")
    funDef = [("d",(["x"],Apply (Fun "g") (Free "x"))), ("g",(["x"],Apply (Fun "d") (Free "x")))]
    expected = (Apply (Fun "d") (Free "x"),[("d",(["x"],Apply (Fun "g") (Free "x"))),("g",(["x"],Apply (Fun "d") (Free "x")))])
    in return $ testGroup "Distiller" [testCase "Distiller: d x = g x, g x = d x" $ distillProg (funTerm, funDef) @?= expected]

test_append_without_cons :: IO TestTree
test_append_without_cons = let
    funTerm = Apply (Apply (Fun "append") (Free "xs")) (Free "ys")
    funDef = [("append",(["xs","ys"],Case (Free "xs") 
        [("Nil",[],Free "ys")
        ,("Cons",["x","xs#"],Con "Cons" [Free "x", Apply (Apply (Fun "append") (Free "xs#")) (Free "ys")])]))]
    result = distillProg (funTerm, funDef)            
    expectedTerm = Apply (Apply (Fun "f'") (Free "xs")) (Free "ys") 
    expectedFunDef = ("f'",(["xs","ys"], Case (Free "xs") 
        [("Nil",[],Free "ys")
        ,("Cons",["x","xs#"],Con "Cons" [Free "x",Apply (Apply (Fun "f'") (Free "xs#")) (Free "ys")])]))           
    in return $ testGroup "Distiller" [testCase "Distiller: append xs ys, term " $ fst result @?= expectedTerm
                                      ,testCase "Distiller: append xs ys, funDef " $ expectedFunDef `elem` snd result @?= True]

test_append :: IO TestTree
test_append = let
    funTerm = Apply (Apply (Fun "append") (Free "xs")) (Free "ys")
    funDef = [("append",(["xs","ys"],Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs#"],Apply (Apply (Fun "append") (Free "xs#")) (Free "ys"))]))]
    result = distillProg (funTerm, funDef)            
    expectedTerm = Apply (Apply (Fun "f'") (Free "xs")) (Free "ys")
    expectedFunDef = ("f'",(["xs","ys"],Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs#"],Apply (Apply (Fun "f'") (Free "xs#")) (Free "ys"))]))            
    in return $ testGroup "Distiller" [testCase "Distiller: append without cons xs ys, term" $ fst result @?= expectedTerm
                                      ,testCase "Distiller: append without cons xs ys, funDef" $ expectedFunDef `elem` snd result @?= True]

test_plus :: IO TestTree
test_plus = let
    funTerm = Apply (Apply (Fun "plus") (Free "x")) (Free "y")
    funDef = [("plus",(["x","y"],Case (Free "x") [("Zero",[],Free "y"),("Succ",["x'"],Con "Succ" [Apply (Apply (Fun "plus") (Free "x'")) (Free "y")])]))]
    result = distillProg (funTerm, funDef)
    expectedTerm = Apply (Apply (Fun "f'") (Free "x")) (Free "y")
    expectedFunDef = ("f'",(["x","y"],Case (Free "x") [("Zero",[],Free "y"),("Succ",["x'"],Con "Succ" [Apply (Apply (Fun "f'") (Free "x'")) (Free "y")])]))
    in return $ testGroup "Distiller" [testCase "Distiller: plus x y, term " $ fst result @?= expectedTerm
                                      ,testCase "Distiller: plus x y, funDef" $ expectedFunDef `elem` snd result @?= True]

test_plusplus :: IO TestTree
test_plusplus = let
    funTerm = Apply (Apply (Fun "plus") (Free "x")) (Free "x")
    funDef = [("plus",(["x","y"],Case (Free "x") [("Zero",[],Free "y"),("Succ",["x'"],Con "Succ" [Apply (Apply (Fun "plus") (Free "x'")) (Free "y")])]))]
    result = distillProg (funTerm, funDef)
    expectedTerm = Apply (Fun "f'") (Free "x")
    expectedFunDef = ("f'",(["x"],Case (Free "x") [("Zero",[],Con "Zero" []),("Succ",["x'"],Con "Succ" [Apply (Apply (Fun "plus") (Free "x'")) (Con "Succ" [Free "x'"])])]))
    in return $ testGroup "Distiller" [testCase "Distiller: plus x x, term " $ fst result @?= expectedTerm
                                      ,testCase "Distiller: plus x x, funDef" $ expectedFunDef `elem` snd result @?= True]
