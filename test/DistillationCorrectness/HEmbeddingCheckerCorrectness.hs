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
    lts1 = qrevLts
    lts2 = renameVarInLts qrevLts ("xs", "xs1")
    in return $ testGroup "HEChecker" [testCase "case xs of Cons(x',xs') => xs'; Nil => Nil" $ isRenaming lts1 lts2 @?= [("xs", "xs2")]
                                      ,testCase "lts1" $ lts1 @?= doLTS0Tr
                                      ,testCase "lts2" $ lts2 @?= doLTS0Tr]

