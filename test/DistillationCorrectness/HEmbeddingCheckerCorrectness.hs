module DistillationCorrectness.HEmbeddingCheckerCorrectness where

import Test.Tasty.Providers (TestTree)
import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TermType
import HelperTypes (renaming, renameVarInLts)
import LTSType
import Residualizer
import Driver (drive)
import InputData  
import HomeomorphicEmbeddingChecker (isRenaming)
    
test_checkRenaming_case :: IO TestTree
test_checkRenaming_case = let 
    lts1 = doLTSManyTr (Apply (Apply (Fun "qrev") (Free "xs")) (Free "ys"))
        [(Apply0', doLTSManyTr (Apply (Fun "qrev") (Free "xs"))
            [(Apply0', qrevLts)
            ,(Apply1', doLTS1Tr (Free "xs") (X' "xs") doLTS0Tr)])
        ,(Apply1', doLTS1Tr (Free "ys") (X' "ys") doLTS0Tr)]
    lts2 = renameVarInLts lts1 ("xs", "xs1")
    in return $ testGroup "HEChecker" [testCase "case xs of Cons(x',xs') => xs'; Nil => Nil" $ isRenaming lts1 lts2 @?= [("xs", "xs1")]
                                      ,testCase "lts1" $ lts1 @?= doLTS0Tr
                                      ,testCase "lts2" $ lts2 @?= doLTS0Tr]

