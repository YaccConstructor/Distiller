module DistillationCorrectness.DrivingCorrectness where
  
import Driver
import LTSType
import TermType
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
    in return $ testGroup "Tests" [testCase "lts from map function" $ drive term ["fun"] [] @?= expectedLts] 


