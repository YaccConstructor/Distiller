module DistillationCorrectness.DrivingCorrectness where
  
import Driver
import LTSType
import TermType
import InputData

import Test.Tasty
import Test.Tasty.HUnit

test_checkDrivingCorrectness1 :: IO TestTree
test_checkDrivingCorrectness1 = let
    expectedLts = LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Free "xs")]) 
                        [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
                        ,(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))
                        ,(CaseBranch' "Cons" ["x","xs"],LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])
    term = Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"], Free "xs")]
    in return $ testGroup "Tests" [testCase "lts1 from term1" $ drive term [] [] @?= expectedLts]

test_checkDrivingCorrectness_apply :: IO TestTree
test_checkDrivingCorrectness_apply = let 
    term = Apply (Fun "fun") (Free "xs")
    expectedLts = doLTSManyTr term [(Apply0', doLTS1Tr (Fun "fun") (Unfold' "fun") doLTS0Tr), (Apply1', doLTS1Tr (Free "xs") (X' "xs") doLTS0Tr)] 
    in return $ testGroup "Tests" [testCase "lts from apply" $ drive term ["fun"] [] @?= expectedLts]

test_checkDrivingCorrectness_append :: IO TestTree
test_checkDrivingCorrectness_append = let
    term = appendTerm
    expectedLts = LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Free "xs"),("Cons",["x'","xs'"],Con "Cons" [Free "x'",Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")])])
        [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
        ,(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
        ,(CaseBranch' "Cons" ["x'","xs'"],LTS (LTSTransitions (Con "Cons" [Free "x'",Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")])
            [(Con' "Cons",Leaf)
            ,(ConArg' "#1",LTS (LTSTransitions (Free "x'") [(X' "x'",Leaf)]))
            ,(ConArg' "#2",LTS (LTSTransitions (Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")) [(Apply0',LTS (LTSTransitions (Apply (Fun "append") (Free "xs'"))
                [(Apply0',LTS (LTSTransitions (Fun "append") [(Unfold' "append",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs'") [(X' "xs'",Leaf)]))]))
                ,(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))]))]))])
    in return $ testGroup "Tests" [testCase "lts from append function" $ drive term ["append"] [] @?= expectedLts]

test_checkDrivingCorrectness_qrev :: IO TestTree
test_checkDrivingCorrectness_qrev = let
    term = Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))]
    expectedLts = LTS (LTSTransitions
        (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))])
        [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
        ,(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))
        ,(CaseBranch' "Cons" ["x","xs"], LTS (LTSTransitions (Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))
        [(Apply0',LTS (LTSTransitions (Apply (Fun "qrev") (Free "xs"))
            [(Apply0',LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",Leaf)]))
            ,(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))]))
        ,(Apply1',LTS (LTSTransitions (Con "Cons" [Free "x",Free "ys"])
            [(Con' "Cons",Leaf)
            ,(ConArg' "#1",LTS (LTSTransitions (Free "x") [(X' "x",Leaf)]))
            ,(ConArg' "#2",LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))]))]))])
    in return $ testGroup "Tests" [testCase "lts from qrev function" $ drive term ["qrev"] [] @?= expectedLts]

test_checkDrivingCorrectness_neil :: IO TestTree
test_checkDrivingCorrectness_neil = let
    neil3Term = Case (Apply (Fun "f") (Free "xs'"))
                         [("True", [],Apply (Fun "f") (Free "xs'"))
                         ,("False", [], Con "False" [])]
    fDef = Case (Free "xs")
        [("Nil",[], Con "True" [])
        ,("Cons",["x","xs"],Case (Apply (Fun "f") (Free "xs")) [("True", [], Apply (Fun "f") (Free "xs")), ("False",[], Con "False" [])])
        ]
    expectedLts = LTS (LTSTransitions (Case (Apply (Fun "f") (Free "xs'")) [("True",[],Apply (Fun "f") (Free "xs'")),("False",[],Con "False" [])]) 
        [(Case',LTS (LTSTransitions (Apply (Fun "f") (Free "xs'")) [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",LTS (LTSTransitions (Case (Free "xs") 
            [("Nil",[],Con "True" []),("Cons",["x","xs"],Case (Apply (Fun "f") (Free "xs")) [("True",[],Apply (Fun "f") (Free "xs")),("False",[],Con "False" [])])]) 
            [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
            ,(CaseBranch' "Nil" [],LTS (LTSTransitions (Con "True" []) [(Con' "True",Leaf)]))
            ,(CaseBranch' "Cons" ["x","xs"],LTS (LTSTransitions (Case (Apply (Fun "f") (Free "xs")) [("True",[],Apply (Fun "f") (Free "xs")),("False",[],Con "False" [])]) 
            [(Case',LTS (LTSTransitions (Apply (Fun "f") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs") 
            [(X' "xs",Leaf)]))])),(CaseBranch' "True" [],LTS (LTSTransitions (Apply (Fun "f") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",Leaf)]))
            ,(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])),(CaseBranch' "False" [],LTS (LTSTransitions (Con "False" []) [(Con' "False",Leaf)]))]))]))]))
            ,(Apply1',LTS (LTSTransitions (Free "xs'") [(X' "xs'",Leaf)]))]))
        ,(CaseBranch' "True" [],LTS (LTSTransitions (Apply (Fun "f") (Free "xs'")) 
            [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Con "True" []),("Cons",["x","xs"],Case (Apply (Fun "f") (Free "xs")) 
            [("True",[],Apply (Fun "f") (Free "xs")),("False",[],Con "False" [])])]) [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)])),(CaseBranch' "Nil" [],
            LTS (LTSTransitions (Con "True" []) [(Con' "True",Leaf)])),(CaseBranch' "Cons" ["x","xs"],LTS (LTSTransitions (Case (Apply (Fun "f") (Free "xs")) [("True",[],Apply (Fun "f") 
            (Free "xs")),("False",[],Con "False" [])]) [(Case',LTS (LTSTransitions (Apply (Fun "f") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",Leaf)]))
            ,(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])),(CaseBranch' "True" [],LTS (LTSTransitions (Apply (Fun "f") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "f") 
            [(Unfold' "f",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])),(CaseBranch' "False" [],LTS (LTSTransitions (Con "False" []) [(Con' "False",Leaf)]))]))]))]))
            ,(Apply1',LTS (LTSTransitions (Free "xs'") [(X' "xs'",Leaf)]))]))
        ,(CaseBranch' "False" [],LTS (LTSTransitions (Con "False" []) [(Con' "False",Leaf)]))])
    in return $ testGroup "Tests" [testCase "lts from qrev function" $ neil3Lts @?= expectedLts]

