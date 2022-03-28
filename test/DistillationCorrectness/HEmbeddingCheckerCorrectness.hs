module DistillationCorrectness.HEmbeddingCheckerCorrectness where

import Test.Tasty.Providers (TestTree)
import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TermType
import DistillationHelpers (termRenaming, renameVarInLts, renameVarInLtsRecursively)
import LTSType
import Residualizer
import Driver (drive)
import InputData  
import HomeomorphicEmbeddingChecker (isRenaming, isHomeomorphicEmbedding)
    
test_checkRenaming_qrev :: IO TestTree
test_checkRenaming_qrev = let
    lts1 = doLTSManyTr (Apply (Apply (Fun "qrev") (Free "xs")) (Free "ys"))
        [(Apply0', doLTSManyTr (Apply (Fun "qrev") (Free "xs"))
            [(Apply0', qrevLts)
            ,(Apply1', doLTS1Tr (Free "xs") (X' "xs") doLTS0Tr)])
        ,(Apply1', doLTS1Tr (Free "ys") (X' "ys") doLTS0Tr)]
    lts2 = renameVarInLts lts1 ("xs", "xs1")
    in return $ testGroup "HEChecker" [testCase "Renaming: qrev xs ys and qrev xs1 ys" $ isRenaming lts1 lts2 @?= [("#","#"),("x","x"),("x'","x'"),("xs","xs1"),("ys","ys")]]

test_checkRenaming_lambda :: IO TestTree
test_checkRenaming_lambda = let
    lts1 = drive (Apply
                   (Apply
                        (Lambda "x" (Lambda "ys" (Lambda "xs" (Case (Free "xs")
                            [("Nil",[],Free "ys")
                            ,("Cons",["x","xs"],(Free "xs"))]))))
                        (Con "Cons" [Free "x",Free "ys"]))
                   (Apply
                        (Apply
                            (Lambda "x" (Lambda "xs" (Case (Free "xs") [("Nil",[],Con "Nil" []),("Cons",["x","xs"],(Free "xs"))])))
                            (Free "xs"))
                        (Con "Nil" []))) [] []
    lts2 = renameVarInLtsRecursively [("xs", "xs1"), ("ys", "ys1")] lts1
    in return $ testGroup "HEChecker" [testCase "Renaming: lambda x ys xs x xs and lambda x ys1 xs1 x xs1" $ isRenaming lts1 lts2 @?= [("x","x"),("xs","xs1"),("ys","ys1")]]

test_checkRenaming_reflexive_f :: IO TestTree
test_checkRenaming_reflexive_f = let
    lts1 = LTS (LTSTransitions (Apply (Fun "f") (Free "x"))
        [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",LTS (LTSTransitions (Apply (Fun "f") (Free "x"))
            [(Apply0',LTS (LTSTransitions (Fun "f") [(Unfold' "f",Leaf)])), (Apply1',LTS (LTSTransitions (Free "x") [(X' "x",Leaf)]))]))]))
            ,(Apply1',LTS (LTSTransitions (Free "x") [(X' "x",Leaf)]))])
    in return $ testGroup "HEChecker" [testCase "Renaming: reflexive f x and f x" $ isRenaming lts1 lts1 @?= [("#", "#"), ("x","x")]]

test_checkRenaming_reflexive_f_with_unfoldBeta :: IO TestTree
test_checkRenaming_reflexive_f_with_unfoldBeta = let
    lts1 = LTS (LTSTransitions (Apply (Fun "f") (Free "x"))
        [(Unfold' "f",LTS (LTSTransitions (Apply (Lambda "x" (Apply (Fun "f") (Free "x"))) (Free "x"))
            [(UnfoldBeta',LTS (LTSTransitions (Apply (Fun "f") (Free "x")) [(Unfold' "f",Leaf)]))]))])
    in return $ testGroup "HEChecker" [testCase "Renaming: reflexive f x and f x with unfold beta" $ isRenaming lts1 lts1 @?= [("#","#")]]

test_checkRenaming :: IO TestTree
test_checkRenaming = let
    lts2 = LTS (LTSTransitions (Apply (Apply (Fun "append") (Free "xs"))
            (Free "ys")) [(Unfold' "append",LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs#"],Apply (Apply (Fun "append") (Free "xs#")) (Free "ys"))])
            [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)])),
            (CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)])),(CaseBranch' "Cons" ["x","xs#"],LTS (LTSTransitions (Apply (Apply (Fun "append") (Free "xs#")) (Free "ys"))
            [(Unfold' "append",Leaf)]))]))])
    lts1 = LTS (LTSTransitions (Apply (Apply (Fun "f") (Free "xs#")) (Free "ys")) [(Unfold' "f",LTS (LTSTransitions
           (Case (Free "xs#") [("Nil",[],Free "ys"),("Cons",["x","xs#"],Apply (Apply (Fun "f") (Free "xs#")) (Free "ys"))])
           [(Case',LTS (LTSTransitions (Free "xs#") [(X' "xs#",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys")
            [(X' "ys",Leaf)])),(CaseBranch' "Cons" ["x","xs#"],LTS (LTSTransitions (Apply (Apply (Fun "f") (Con "Cons" [Free "x",Free "xs#"])) (Free "ys"))
            [(Unfold' "f",Leaf)]))]))])
    in return $ testGroup "HEChecker" [testCase "Renaming: reflexive f x and f x with unfold beta" $ isRenaming lts1 lts2 @?= [("xs#","xs"),("ys","ys")]]

test_checkRenaming1 :: IO TestTree
test_checkRenaming1 = let
    lts = LTS (LTSTransitions (Apply (Apply (Fun "f") (Free "xs")) (Free "ys")) 
        [(Unfold' "f",LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs#"],Apply (Apply (Fun "f") (Free "xs#")) (Free "ys"))]) 
            [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
            ,(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))
            ,(CaseBranch' "Cons" ["x","xs#"],LTS (LTSTransitions (Apply (Apply (Fun "f") (Free "xs#")) (Free "ys")) [(Unfold' "f",Leaf)]))]))])     
    in return $ testGroup "HEChecker" [testCase "Renaming: reflexive f xs ys and f xs ys" $ isRenaming lts lts @?= [("#","#"),("xs","xs"),("ys","ys")]]

test_checkRenaming2 :: IO TestTree
test_checkRenaming2 = let
    lts = LTS (LTSTransitions (Case (Free "x") [("True",[],Con "False" []),("False",[],Con "False" [])]) [(Case',LTS (LTSTransitions (Free "x") [(X' "x",Leaf)])),(CaseBranch' "True" [],
          LTS (LTSTransitions (Con "False" []) [(Con' "False",Leaf)])),(CaseBranch' "False" [],LTS (LTSTransitions (Con "False" []) [(Con' "False",Leaf)]))]) 
    in return $ testGroup "HEChecker" [testCase "Renaming: reflexive case x and case x" $ isRenaming lts lts @?= [("x","x")]]

test_checkEmbedding :: IO TestTree
test_checkEmbedding = let 
   lts1 = LTS (LTSTransitions (Apply (Apply (Fun "f''") (Free "xs#")) (Free "ys")) [(Unfold' "f''",LTS (LTSTransitions (Case (Free "xs#") [("Nil",[],Free "ys"),
          ("Cons",["x","xs#'"],Apply (Apply (Fun "f''") (Free "xs#'")) (Free "ys"))]) [(Case',LTS (LTSTransitions (Free "xs#") [(X' "xs#",Leaf)])),(CaseBranch' "Nil" [],
          LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)])),(CaseBranch' "Cons" ["x","xs#'"],LTS (LTSTransitions (Apply (Apply (Fun "f''") (Free "xs#'")) (Free "ys")) 
          [(Unfold' "f''",Leaf)]))]))])  
   in return $ testGroup "HEChecker" [testCase "Renaming: reflexive case x and case x" $ isRenaming lts1 lts1 @?= [("#","#"),("xs#","xs#"),("ys","ys")]]

test_checkEmbedding_qrev :: IO TestTree
test_checkEmbedding_qrev = let
    lts1 = qrevLts
    lts2 = qrevLts'
    in return $ testGroup "HEChecker" [testCase "HEmbedding: qrev lts2 lts1" $ isHomeomorphicEmbedding lts2 lts1 @?= [("x","x"),("xs","xs"),("x","x'"),("xs","xs")]
                                      ,testCase "HEmbedding: qrev lts1 lts2" $ isHomeomorphicEmbedding lts1 lts2 @?= []]
    
test_checkEmbedding_swap_qrev :: IO TestTree
test_checkEmbedding_swap_qrev = let 
    lts1 = swapQrevLts
    lts2 = swapQrevLts'
    in return $ testGroup "HEChecker" [testCase "HEmbedding: swap qrev lts2 lts1" $ isHomeomorphicEmbedding lts2 lts1 @?= [("y","y"),("ys","ys"),("y","y'"),("ys","ys")]
                                      ,testCase "HEmbedding: swap qrev lts1 lts2" $ isHomeomorphicEmbedding lts1 lts2 @?= []]

test_checkEmbedding_neil3 :: IO TestTree
test_checkEmbedding_neil3 = let
    lts1 = neil3Lts
    lts2 = neil3Lts'
    in return $ testGroup "HEChecker" [testCase "HEmbedding: neil3 lts1 lts2" $ isHomeomorphicEmbedding lts1 lts2 @?= [("xs'","xs''"),("xs","xs")]
                                      ,testCase "HEmbedding: neil3 lts2 lts1" $ isHomeomorphicEmbedding lts2 lts1 @?= []]

test_checkEmbedding_append :: IO TestTree
test_checkEmbedding_append = let
    lts1 = appendLts
    lts2 = appendLts'
    in return $ testGroup "HEChecker" [testCase "HEmbedding: append lts1 lts2" $ isHomeomorphicEmbedding lts1 lts2 @?= [("x'","x''"),("xs'","xs''"),("xs","xs'")]
                                      ,testCase "HEmbedding: append lts2 lts1" $ isHomeomorphicEmbedding lts2 lts1 @?= []]
    
test_checkEmbedding_revrev :: IO TestTree
test_checkEmbedding_revrev = let 
    lts111111 = revrevTermLts
    lts222222 = revrevTermLts'
    lts11111 = drive (Case (Apply (Apply (Fun "append") (Free "xs'"))
                        (Con "Con" [Free "x'", Con "Nil" []]))
                   [("Nil", [], (Con "Con" [Free "x'", Con "Nil" []]))
                   ,("Con",["x","xs"], Con "Con" [Free "x", Apply (Apply (Fun "append") (Free "xs")) (Con "Con" [Free "x'", Con "Nil" []])])]) ["append"] []
    lts22222 = drive (Case (Apply (Apply (Fun "append") (Free "xs''"))
                    (Con "Con" [Free "x''", Con "Con" [Free "x'", Con "Nil" []]]))
                   [("Nil", [], (Con "Con" [Free "x'", Con "Nil" []]))
                   ,("Con",["x","xs"], Con "Con" [Free "x", Apply (Apply (Fun "append") (Free "xs")) (Con "Con" [Free "x'", Con "Nil" []])])]) ["append"] []
    lts1111 = drive (Case (Con "Con" [Free "x'", Con "Nil" []])
                                    [("Nil", [], (Con "Con" [Free "x'", Con "Nil" []]))
                                    ,("Con",["x","xs"], Con "Con" [Free "x", Apply (Apply (Fun "append") (Free "xs")) (Con "Con" [Free "x'", Con "Nil" []])])]) ["append"] []
    lts2222 = drive (Case (Con "Con" [Free "x''", Con "Con" [Free "x'", Con "Nil" []]])
                                    [("Nil", [], (Con "Con" [Free "x'", Con "Nil" []]))
                                    ,("Con",["x","xs"], Con "Con" [Free "x", Apply (Apply (Fun "append") (Free "xs")) (Con "Con" [Free "x'", Con "Nil" []])])]) ["append"] []
    lts111 = drive (Case (Con "Con" [Free "x'", Con "Nil" []])
                                        [("Nil", [], (Con "Con" [Free "x'", Con "Nil" []]))
                                        ,("Con",["x","xs"], Con "Con" [Free "x", (Con "Con" [Free "x'", Con "Nil" []])])]) ["append"] []
    lts222 = drive (Case (Con "Con" [Free "x''", Con "Con" [Free "x'", Con "Nil" []]])
                                        [("Nil", [], (Con "Con" [Free "x'", Con "Nil" []]))
                                        ,("Con",["x","xs"], Con "Con" [Free "x", (Con "Con" [Free "x'", Con "Nil" []])])]) ["append"] []
    lts11 = drive (Case (Con "Con" [Free "x'", Con "Nil" []])
                    [("Nil", [], Con "Nil" [])
                    ,("Con",["x","xs"], (Con "Con" [Free "x'", Con "Nil" []]))])    [] []
    lts22 = drive (Case (Con "Con" [Free "x''", Con "Con" [Free "x'", Con "Nil" []]])
                    [("Nil", [], Con "Nil" [])
                    ,("Con",["x","xs"], (Con "Con" [Free "x'", Con "Nil" []]))])   [] []
    lts1 = drive ((Apply (Apply (Fun "f") ((Con "Con" [Free "x'", Con "Nil" []]))) ((Free "x''")))) ["f"] []
    lts2 = drive ((Apply (Apply (Fun "f") (Con "Con" [Free "x''", Con "Con" [Free "x'", Con "Nil" []]])) ((Free "x''")))) ["f"] []
    in return $ testGroup "HEChecker" [testCase "HEmbedding: revrev lts1 lts2" $ isHomeomorphicEmbedding lts1 lts2 @?= [("x''","x''"),("x'","x'"),("x''","x''"),("x'","x''")]
                                      ,testCase "HEmbedding: revrev lts11 lts22" $ isHomeomorphicEmbedding lts11 lts22 @?= [("x'","x'")]
                                      ,testCase "HEmbedding: revrev lts111 lts222" $ isHomeomorphicEmbedding lts111 lts222 @?= [("x", "x"), ("x'","x'")]
                                      ,testCase "HEmbedding: revrev lts1111 lts2222" $ isHomeomorphicEmbedding lts1111 lts2222 @?= [("x","x"),("xs","xs"),("x'","x'")]
                                      ,testCase "HEmbedding: revrev lts11111 lts22222" $ isHomeomorphicEmbedding lts11111 lts22222 @?= [("x","x"),("xs","xs"),("x'","x'"),("xs'","xs''")]
                                      ,testCase "HEmbedding: revrev lts111111 lts222222" $ isHomeomorphicEmbedding lts111111 lts222222 @?= [("x","x"),("xs","xs"),("x'","x'"),("xs'","xs''")]
                                      ,testCase "HEmbedding: revrev lts2 lts1" $ isHomeomorphicEmbedding lts2 lts1 @?= []
                                      ,testCase "HEmbedding: revrev lts22 lts11" $ isHomeomorphicEmbedding lts22 lts11 @?= []
                                      ,testCase "HEmbedding: revrev lts222 lts111" $ isHomeomorphicEmbedding lts222 lts111 @?= []
                                      ,testCase "HEmbedding: revrev lts2222 lts1111" $ isHomeomorphicEmbedding lts2222 lts1111 @?= []
                                      ,testCase "HEmbedding: revrev lts22222 lts11111" $ isHomeomorphicEmbedding lts22222 lts11111 @?= []
                                      ,testCase "HEmbedding: revrev lts222222 lts111111" $ isHomeomorphicEmbedding lts222222 lts111111 @?= []]

test_checkEmbedding_nested_cases :: IO TestTree
test_checkEmbedding_nested_cases = let
    lts1 = term1Lts
    lts2 = term2Lts
    in return $ testGroup "HEChecker" [testCase "HEmbedding: nested cases lts1 lts2" $ isHomeomorphicEmbedding lts1 lts2 @?= [("x'","x'"),("v'","v'"),("vs'","vs'"),("xs'","xs''")]
                                      ,testCase "HEmbedding: nested cases lts2 lts1" $ isHomeomorphicEmbedding lts2 lts1 @?= []]
                                      
test_check_nested_constructors :: IO TestTree
test_check_nested_constructors = let 
    lts1 = drive ((Con "Con" [Free "x'", Con "Nil" []])) [] []
    lts2 = drive ((Con "Con" [Free "x''", Con "Con" [Free "x'", Con "Nil" []]])) [] []
    in return $ testGroup "HEChecker" [testCase "HEmbedding: nested constructors lts1 lts2" $ isHomeomorphicEmbedding lts1 lts2 @?= [("x'", "x''")]
                                      ,testCase "HEmbedding: nested constructors lts2 lts1" $ isHomeomorphicEmbedding lts2 lts1 @?= []]
                                                                                    