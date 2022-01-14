module DistillationCorrectness.GeneralizationCorrectness where

import Generalizer
import Driver
import LTSType
import TermType
import InputData

import Test.Tasty
import Test.Tasty.HUnit
import Debug.Trace (trace)

test_checkGeneralizationCorrectness :: IO TestTree
test_checkGeneralizationCorrectness  = let
  expectedLts = LTS (LTSTransitions (Fun "qrev") 
        [(Let',LTS (LTSTransitions (Fun "qrev") 
            [(Unfold' "qrev",LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Con "Nil" []),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Con "Nil" []]))]) 
                [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
                ,(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "x2") [(X' "x2",Leaf)]))
                ,(CaseBranch' "Cons" ["x","xs"],LTS (LTSTransitions (Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Con "Nil" []])) 
                    [(Apply0',LTS (LTSTransitions (Apply (Fun "qrev") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))]))
                    ,(Apply1',LTS (LTSTransitions (Con "Cons" [Free "x",Con "Nil" []]) 
                        [(Con' "Cons",Leaf)
                        ,(ConArg' "#1",LTS (LTSTransitions (Free "x") [(X' "x",Leaf)]))
                        ,(ConArg' "#2",LTS (LTSTransitions (Free "x2") [(X' "x2",Leaf)]))]))]))]))]))
        ,(X' "x2",LTS (LTSTransitions (Con "Nil" []) [(Con' "Nil",Leaf)]))])
  in return $ testGroup "Tests" [testCase "qrev xs [] & qrev xs ys" $ generalize qrevLts' qrevLts [] @?= expectedLts]

test_checkGeneralizationCorrectness_qrev_swap :: IO TestTree
test_checkGeneralizationCorrectness_qrev_swap = let
  expectedLts = LTS (LTSTransitions (Fun "qrev") 
        [(Let',LTS (LTSTransitions (Fun "qrev") 
            [(Unfold' "qrev",LTS (LTSTransitions (Case (Free "ys") [("Nil",[],Con "Nil" []),("Cons",["y","ys"],Apply (Apply (Fun "qrev") (Free "ys")) (Con "Cons" [Free "y",Con "Nil" []]))]) 
                [(Case',LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "x2") [(X' "x2",Leaf)]))
                ,(CaseBranch' "Cons" ["y","ys"],LTS (LTSTransitions (Apply (Apply (Fun "qrev") (Free "ys")) (Con "Cons" [Free "y",Con "Nil" []])) 
                    [(Apply0',LTS (LTSTransitions (Apply (Fun "qrev") (Free "ys")) [(Apply0',LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",Leaf)])),(Apply1',LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))]))
                    ,(Apply1',LTS (LTSTransitions (Con "Cons" [Free "y",Con "Nil" []]) 
                        [(Con' "Cons",Leaf)
                        ,(ConArg' "#1",LTS (LTSTransitions (Free "y") [(X' "y",Leaf)]))
                        ,(ConArg' "#2",LTS (LTSTransitions (Free "x2") [(X' "x2",Leaf)]))]))]))]))]))
        ,(X' "x2",LTS (LTSTransitions (Con "Nil" []) [(Con' "Nil",Leaf)]))])
  in return $ testGroup "Tests" [testCase "qrev [] ys & qrev xs ys" $ generalize swapQrevLts' swapQrevLts [] @?= expectedLts]

test_checkGeneralizationCorrectness_append :: IO TestTree
test_checkGeneralizationCorrectness_append = let
    expectedLts = LTS (LTSTransitions (Fun "append")
        [(Let',LTS (LTSTransitions (Fun "append") [(Unfold' "append",
        LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Free "xs"),("Cons",["x'","xs'"],Con "Cons" [Free "x'",Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")])])
        [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "x2") [(X' "x2",Leaf)])),(CaseBranch' "Cons" ["x'","xs'"],
        LTS (LTSTransitions (Con "Cons" [Free "x'",Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")]) [(Con' "Cons",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x'")
        [(X' "x'",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")) [(Apply0',LTS (LTSTransitions (Apply (Fun "append") (Free "xs'"))
        [(Apply0',LTS (LTSTransitions (Fun "append") [(Unfold' "append",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs'") [(X' "xs'",Leaf)]))])),(Apply1',LTS (LTSTransitions (Free "x2")
        [(X' "x2",Leaf)]))]))]))]))]))
        ,(X' "x2",LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])
    in do return $ testGroup "Tests" [testCase "append xs xs & append xs Cons(x,xs)" $ generalize appendLts appendLts' [] @?= expectedLts]

test_checkGeneralizationCorrectness_neil3 :: IO TestTree
test_checkGeneralizationCorrectness_neil3 = let
    expectedLts = LTS (LTSTransitions (Case (Apply (Fun "f") (Free "xs'")) [("True",[],Apply (Fun "f") (Free "xs'")),("False",[],Con "False" [])])
        [(Let',LTS (LTSTransitions (Case (Apply (Fun "f") (Free "xs'")) [("True",[],Apply (Fun "f") (Free "xs'")),("False",[],Con "False" [])]) [(Case',LTS (LTSTransitions (Free "x1")
        [(X' "x1",Leaf)])),(CaseBranch' "True" [],LTS (LTSTransitions (Apply (Fun "f") (Free "xs'")) [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",LTS (LTSTransitions (Case (Free "xs")
        [("Nil",[],Con "True" []),("Cons",["x","xs"],Case (Apply (Fun "f") (Free "xs")) [("True",[],Apply (Fun "f") (Free "xs")),("False",[],Con "False" [])])])
        [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Con "True" []) [(Con' "True",Leaf)])),(CaseBranch' "Cons" ["x","xs"],
        LTS (LTSTransitions (Case (Apply (Fun "f") (Free "xs")) [("True",[],Apply (Fun "f") (Free "xs")),("False",[],Con "False" [])]) [(Case',LTS (LTSTransitions (Apply (Fun "f") (Free "xs"))
        [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])),(CaseBranch' "True" [],
        LTS (LTSTransitions (Apply (Fun "f") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))]))
        ,(CaseBranch' "False" [],LTS (LTSTransitions (Con "False" []) [(Con' "False",Leaf)]))]))]))])),(Apply1',LTS (LTSTransitions (Free "x2") [(X' "x2",Leaf)]))])),(CaseBranch' "False" []
        ,LTS (LTSTransitions (Con "False" []) [(Con' "False",Leaf)]))]))

        ,(X' "x1",LTS (LTSTransitions (Apply (Fun "f") (Free "xs'")) [(Apply0',LTS (LTSTransitions (Fun "f")
        [(Unfold' "f",LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Con "True" []),("Cons",["x","xs"],Case (Apply (Fun "f") (Free "xs")) [("True",[],Apply (Fun "f") (Free "xs"))
        ,("False",[],Con "False" [])])]) [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Con "True" []) [(Con' "True",Leaf)]))
        ,(CaseBranch' "Cons" ["x","xs"],LTS (LTSTransitions (Case (Apply (Fun "f") (Free "xs")) [("True",[],Apply (Fun "f") (Free "xs")),("False",[],Con "False" [])])
        [(Case',LTS (LTSTransitions (Apply (Fun "f") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs")
        [(X' "xs",Leaf)]))])),(CaseBranch' "True" [],LTS (LTSTransitions (Apply (Fun "f") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",Leaf)]))
        ,(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])),(CaseBranch' "False" [],LTS (LTSTransitions (Con "False" []) [(Con' "False",Leaf)]))]))]))]))
        ,(Apply1',LTS (LTSTransitions (Free "xs'") [(X' "xs'",Leaf)]))]))

        ,(X' "x2",LTS (LTSTransitions (Free "xs'") [(X' "xs'",Leaf)]))])
    in do return $ testGroup "Tests" [testCase "neil3" $ generalize neil3Lts neil3Lts' [] @?= expectedLts]

test_checkGeneralizationCorrectness_revrev :: IO TestTree
test_checkGeneralizationCorrectness_revrev  = let
    expectedLts = LTS (LTSTransitions (Case (Apply (Apply (Fun "append") (Apply (Apply (Fun "revrev") (Free "xs''")) 
        (Con "Cons" [Free "x''",Free "x'"]))) (Con "Con" [Free "x''",Con "Nil" []])) [("Nil",[],Con "Con" [Free "x'",Con "Nil" []])
        ,("Con",["x","xs"],Con "Con" [Free "x",Apply (Apply (Fun "append") (Free "xs")) (Con "Con" [Free "x'",Con "Nil" []])])]) 
        [(Let',LTS (LTSTransitions (Case (Apply (Apply (Fun "append") (Apply (Apply (Fun "revrev") (Free "xs''")) (Con "Cons" 
        [Free "x''",Free "x'"]))) (Con "Con" [Free "x''",Con "Nil" []])) [("Nil",[],Con "Con" [Free "x'",Con "Nil" []]),("Con",["x","xs"]
        ,Con "Con" [Free "x",Apply (Apply (Fun "append") (Free "xs")) (Con "Con" [Free "x'",Con "Nil" []])])]) [(Case',LTS (LTSTransitions 
        (Apply (Apply (Fun "append") (Apply (Apply (Fun "revrev") (Free "xs''")) (Con "Cons" [Free "x''",Free "x'"]))) (Con "Con"
         [Free "x''",Con "Nil" []])) [(Apply0',LTS (LTSTransitions (Apply (Fun "append") (Apply (Apply (Fun "revrev") (Free "xs''")) 
         (Con "Cons" [Free "x''",Free "x'"]))) [(Apply0',LTS (LTSTransitions (Fun "append") [(Unfold' "append",LTS (LTSTransitions (Free "x3")
          [(X' "x3",Leaf)]))])),(Apply1',LTS (LTSTransitions (Free "x2") [(X' "x2",Leaf)]))])),(Apply1',LTS (LTSTransitions (Con "Con" 
          [Free "x''",Con "Nil" []]) [(Con' "Con",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x''") [(X' "x''",Leaf)])),(ConArg' "#2",LTS 
          (LTSTransitions (Con "Nil" []) [(Con' "Nil",Leaf)]))]))])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Con "Con" [Free "x'",Con "Nil" []])
           [(Con' "Con",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x'") [(X' "x'",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Con "Nil" []) 
           [(Con' "Nil",Leaf)]))])),(CaseBranch' "Con" ["x","xs"],LTS (LTSTransitions (Con "Con" [Free "x",Apply (Apply (Fun "append") (Free "xs")) 
           (Con "Con" [Free "x'",Con "Nil" []])]) [(Con' "Con",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x") [(X' "x",Leaf)])),(ConArg' "#2"
           ,LTS (LTSTransitions (Apply (Apply (Fun "append") (Free "xs")) (Con "Con" [Free "x'",Con "Nil" []])) [(Apply0',LTS (LTSTransitions (Apply 
           (Fun "append") (Free "xs")) [(Apply0',LTS (LTSTransitions (Fun "append") [(Unfold' "append",LTS (LTSTransitions (Free "x3")
            [(X' "x3",Leaf)]))])),(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])),(Apply1',LTS (LTSTransitions (Con "Con"
             [Free "x'",Con "Nil" []]) [(Con' "Con",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x'") [(X' "x'",Leaf)])),(ConArg' "#2",LTS 
             (LTSTransitions (Con "Nil" []) [(Con' "Nil",Leaf)]))]))]))]))]))
             
             ,(X' "x3",Leaf)
             ,(X' "x2",LTS (LTSTransitions (Apply (Apply 
             (Fun "revrev") (Free "xs''")) (Con "Cons" [Free "x''",Free "x'"])) [(Apply0',LTS (LTSTransitions (Apply (Fun "revrev") (Free "xs''"))
              [(Apply0',LTS (LTSTransitions (Fun "revrev") [(Unfold' "revrev",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs''") 
              [(X' "xs''",Leaf)]))])),(Apply1',LTS (LTSTransitions (Con "Cons" [Free "x''",Free "x'"]) [(Con' "Cons",Leaf)
        ,(ConArg' "#1",LTS (LTSTransitions (Free "x''") [(X' "x''",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Free "x'") [(X' "x'",Leaf)]))]))]))])
    in do return $ testGroup "Tests" [testCase "revrev" $ generalize revrevTermLts' revrevTermLts [] @?= expectedLts]

test_checkGeneralizationCorrectness_nested_cases :: IO TestTree
test_checkGeneralizationCorrectness_nested_cases  = let
    expectedTS = 
      LTS (LTSTransitions (Case (Case (Apply (Fun "f") (Free "xs''")) [("Nil",[],Con "Con" [Free "x''",Con "Nil" []]),("Cons",["v'","vs'"] ,Con "Con" [Free "v'",Apply (Fun "g") (Free "vs'")])]) [("Nil",[],Con "Con" [Free "x'",Con "Nil" []]),("Cons",["v'","vs'"],
        Con "Con" [Free "v'",Apply (Fun "g") (Free "vs'")])]) 
    
        [(Let',LTS (LTSTransitions (Case (Case (Apply (Fun "f") (Free "xs''")) 
        [("Nil",[],Con "Con" [Free "x''",Con "Nil" []]),("Cons",["v'","vs'"],Con "Con" [Free "v'",Apply (Fun "g") (Free "vs'")])]) 
        [("Nil",[],Con "Con" [Free "x'",Con "Nil" []]),("Cons",["v'","vs'"],Con "Con" [Free "v'",Apply (Fun "g") (Free "vs'")])])
        [(Case',LTS (LTSTransitions (Free "x1") [(X' "x1",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Con "Con" [Free "x'",Con "Nil" []])
        [(Con' "Con",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x'") [(X' "x'",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Con "Nil" [])
        [(Con' "Nil",Leaf)]))])),(CaseBranch' "Cons" ["v'","vs'"],LTS (LTSTransitions (Con "Con" [Free "v'",Apply (Fun "g") (Free "vs'")]) 
        [(Con' "Con",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "v'") [(X' "v'",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Apply (Fun "g") 
        (Free "vs'")) [(Apply0',LTS (LTSTransitions (Fun "g") [(Unfold' "g",LTS (LTSTransitions (Free "x2") [(X' "x2",Leaf)]))]))
        ,(Apply1',LTS (LTSTransitions (Free "vs'") [(X' "vs'",Leaf)]))]))]))]))
       
       ,(X' "x1",LTS (LTSTransitions (Case (Apply (Fun "f") (Free "xs''")) 
       [("Nil",[],Con "Con" [Free "x''",Con "Nil" []]),("Cons",["v'","vs'"],Con "Con" [Free "v'",Apply (Fun "g") (Free "vs'")])]) 
       [(Case',LTS (LTSTransitions (Apply (Fun "f") (Free "xs''")) [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",Leaf)]))
       ,(Apply1',LTS (LTSTransitions (Free "xs''") [(X' "xs''",Leaf)]))]))
       ,(CaseBranch' "Nil" [],LTS (LTSTransitions 
       (Con "Con" [Free "x''",Con "Nil" []]) [(Con' "Con",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x''") [(X' "x''",Leaf)]))
       ,(ConArg' "#2",LTS (LTSTransitions (Con "Nil" []) [(Con' "Nil",Leaf)]))]))
       ,(CaseBranch' "Cons" ["v'","vs'"],LTS (LTSTransitions 
       (Con "Con" [Free "v'",Apply (Fun "g") (Free "vs'")]) [(Con' "Con",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "v'") [(X' "v'",Leaf)]))
       ,(ConArg' "#2",LTS (LTSTransitions (Apply (Fun "g") (Free "vs'")) [(Apply0',LTS (LTSTransitions (Fun "g") [(Unfold' "g",Leaf)]))
       ,(Apply1',LTS (LTSTransitions (Free "vs'") [(X' "vs'",Leaf)]))]))]))]))
       ,(X' "x2",Leaf)])        
    in do return $ testGroup "Tests" [testCase "nested cases" $ generalize term2Lts term1Lts [] @?= expectedTS]


