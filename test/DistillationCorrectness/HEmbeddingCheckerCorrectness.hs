module DistillationCorrectness.HEmbeddingCheckerCorrectness where

import Test.Tasty.Providers (TestTree)
import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TermType
import HelperTypes (termRenaming, renameVarInLts, renameVarInLtsRecursively)
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
    in return $ testGroup "HEChecker" [testCase "Renaming: qrev xs ys and qrev xs1 ys" $ isRenaming lts1 lts2 @?= [("xs", "xs1")]]

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
    in return $ testGroup "HEChecker" [testCase "Renaming: lambda x ys xs x xs and lambda x ys1 xs1 x xs1" $ isRenaming lts1 lts2 @?= [("xs", "xs1"), ("ys", "ys1")]]

test_checkEmbedding_qrev :: IO TestTree
test_checkEmbedding_qrev = let
    lts1 = qrevLts
    lts2 = qrevLts'
    in return $ testGroup "HEChecker" [testCase "HEmbedding: qrev" $ isHomeomorphicEmbedding lts2 lts1 @?= [("x","x"),("x","x'"),("xs","xs")]]
    
test_checkEmbedding_swap_qrev :: IO TestTree
test_checkEmbedding_swap_qrev = let 
    lts1 = swapQrevLts
    lts2 = swapQrevLts'
    in return $ testGroup "HEChecker" [testCase "HEmbedding: swap qrev" $ isHomeomorphicEmbedding lts2 lts1 @?= [("y","y"),("y","y'"),("ys","ys")]]

test_checkEmbedding_neil3 :: IO TestTree
test_checkEmbedding_neil3 = let
    lts1 = neil3Lts
    lts2 = neil3Lts'
    in return $ testGroup "HEChecker" [testCase "HEmbedding: neil3" $ isHomeomorphicEmbedding lts1 lts2 @?= [("xs","xs"),("xs'","x'"),("xs'","xs"),("xs'","xs''")]]

test_checkEmbedding_append :: IO TestTree
test_checkEmbedding_append = let
    lts1 = appendLts
    lts2 = appendLts'
    in return $ testGroup "HEChecker" [testCase "HEmbedding: append" $ isHomeomorphicEmbedding lts1 lts2 @?= [("x'","x''"),("xs","x'"),("xs","xs'"),("xs","xs''"),("xs'","xs''")]]
    
test_checkEmbedding_revrev :: IO TestTree
test_checkEmbedding_revrev = let 
    lts1 = revrevTermLts
    lts2 = revrevTermLts'
    in return $ testGroup "HEChecker" [testCase "HEmbedding: revrev" $ isHomeomorphicEmbedding lts1 lts2 @?= [("x","x"),("x","x'"),("x'","x'"),("x'","x''"),("xs","xs")]]

test_checkEmbedding_nested_cases :: IO TestTree
test_checkEmbedding_nested_cases = let
    lts1 = term1Lts
    lts2 = term2Lts
    in return $ testGroup "HEChecker" [testCase "HEmbedding: nested cases" $ isHomeomorphicEmbedding lts1 lts2 @?= [("v'","v'"),("vs'","vs'"),("x'","x'"),("xs'","xs''")]]