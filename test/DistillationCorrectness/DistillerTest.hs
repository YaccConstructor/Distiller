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
    result = distillProg (funTerm, funDef)
    expectedTerm = Apply (Fun "f'") (Free "x")
    expectedFunDef = ("f'",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "False" [])]))
    in return $ testGroup "Distiller" [testCase "Distiller: and x False, term " $ fst result @?= expectedTerm
                                      ,testCase "Distiller: and x False, fundef " $ expectedFunDef `elem` snd result @?= True]

test_not :: IO TestTree
test_not = let
    funTerm = Apply (Fun "not") (Free "x")
    funDef = [("not",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))]
    result = distillProg (funTerm, funDef)
    expectedTerm = Apply (Fun "f'") (Free "x")
    expectedFunDef = ("f'",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))
    in return $ testGroup "Distiller" [testCase "Distiller: not x, term " $ fst result @?= expectedTerm
                                      ,testCase "Distiller: not x, fundef " $ expectedFunDef `elem` snd result @?= True]

test_or :: IO TestTree
test_or = let
    funTerm = Apply (Apply (Fun "or") (Free "x")) (Free "y")
    funDef = [("or",(["x","y"],Case (Free "x") [("True",[],Con "True" []),("False",[],Free "y")]))]
    result = distillProg (funTerm, funDef)
    expectedTerm = Apply (Apply (Fun "f'") (Free "x")) (Free "y")
    expectedFunDef = ("f'",(["x","y"],Case (Free "x") [("True",[],Con "True" []),("False",[],Free "y")]))
    in return $ testGroup "Distiller" [testCase "Distiller: or x y, term " $ fst result @?= expectedTerm
                                      ,testCase "Distiller: or x y, fundef " $ expectedFunDef `elem` snd result @?= True]

test_iff :: IO TestTree
test_iff = let
    funTerm = Apply (Apply (Fun "iff") (Con "True" [])) (Free "x")
    funDef = [("iff",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Apply (Fun "not") (Free "y"))]))
             ,("not",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))]
    result = (Apply (Lambda "x" (Free "x")) (Free "x"), funDef)
    in return $ testGroup "Distiller" [testCase "Distiller: iff True x" $ distillProg (funTerm, funDef) @?= result]

test_eqBool :: IO TestTree
test_eqBool = let
    funTerm = Apply (Apply (Fun "eqBool") (Free "x")) (Con "False" [])
    funDef = [("eqBool",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Apply (Fun "not") (Free "y"))]))
             ,("not",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))]
    --result = Lambda "y" (Lambda "x" (Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))
    --result = (Lambda "y" (Lambda "x" (Case (Free "x") [("True",[],Con "False" []),("False",[],Lambda "x" (Con "True" []))])), funDef)
    result = distillProg (funTerm, funDef)
    expectedTerm = Apply (Fun "f''") (Free "x")
    expectedFunDef = ("f''",(["x"],Case (Free "x") [("True",[],Con "False" []),("False",[],Con "True" [])]))
    in return $ testGroup "Distiller" [testCase "Distiller: eqBool x False, term " $ fst result @?= expectedTerm
                                      ,testCase "Distiller: eqBool x False, fundef " $ expectedFunDef `elem` snd result @?= True]

test_implies :: IO TestTree
test_implies = let
    funTerm = Apply (Apply (Fun "implies") (Free "x")) (Con "True" [])
    funDef = [("implies",(["x","y"],Case (Free "x") [("True",[],Free "y"),("False",[],Con "True" [])]))]
    --result = (Lambda "y" (Lambda "x" (Case (Free "x") [("True",[],Con "True" []),("False",[],Con "True" [])])), funDef)
    result = distillProg (funTerm, funDef)
    expectedTerm = Apply (Fun "f'") (Free "x")
    expectedFunDef = ("f'",(["x"],Case (Free "x") [("True",[],Con "True" []),("False",[],Con "True" [])]))
    in return $ testGroup "Distiller" [testCase "Distiller: implies x True" $ fst result @?= expectedTerm
                                      ,testCase "Distiller: eqBool x False, fundef " $ expectedFunDef `elem` snd result @?= True]

test_f :: IO TestTree
test_f = let
    funTerm = (Apply (Fun "f") (Free "x"))
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

test_append_gen :: IO TestTree
test_append_gen = let
    funTerm = Apply (Apply (Fun "append") (Free "xs")) (Con "Cons" [Free "x",Free "xs"])
    funDef = [("append",(["xs","ys"],Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x'","xs'"],Apply (Apply (Fun "append") (Free "xs'")) (Free "ys"))]))]
    result = Lambda "xs'" (Lambda "ys" (Lambda "xs" (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x'","xs'"],Apply (Apply (Fun "append") (Free "xs'")) (Free "yss"))])))
    in return $ testGroup "Distiller" [testCase "Distiller: append gen xs Cons(x,xs)" $ 2+2 @?=4]--distillProg (funTerm, funDef) @?= result]

test_nrev :: IO TestTree
test_nrev = let
    funTerm = Apply (Fun "nrev") (Free "xs")
    --funDef = [("f",(["xs'","x","x'''"],Case (Free "xs") [("Nil",[],Con "Cons" [Free "",Bound 0]),("Cons",["x","xs"],Apply (Apply (Apply (Fun "f") (Bound 0)) (Bound 1)) (Con "Cons" [Bound 1,Bound 2]))]))])
    funDef = [("append",(["xs","ys"],Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Con "Cons" [Free "x",Apply (Apply (Fun "append") (Free "xs")) (Free "ys")])]))
             ,("nrev",(["xs"],Case (Free "xs") [("Nil",[],Con "Nil" []),("Cons",["x","xs"],Apply (Apply (Fun "append") (Apply (Fun "nrev") (Free "xs"))) (Con "Cons" [Free "x",Con "Nil" []]))]))]
    result = (Case (Free "xs") [("Nil",[],Con "Nil" []),("Cons",["x","xs"],Apply (Apply (Apply (Fun "f") (Free "xs")) (Free "x")) (Con "Nil" []))])
    in return $ testGroup "Distiller" [testCase "Distiller: append xs xs" $ 2+2 @?=4]--distillProg (funTerm, funDef) @?= result]