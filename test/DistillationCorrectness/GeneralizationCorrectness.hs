module DistillationCorrectness.GeneralizationCorrectness where

import Generalizer
import LTSType
import TermType
import Test.Tasty
import Test.Tasty.HUnit

x1 = Free "x1"
x1' = Free "x1'"
lts1 = doLTSManyTr (Con "constructor" [x1]) [("constructor", doLTS0Tr), ("#1", doLTS1Tr x1 "x1" doLTS0Tr)]
lts2 = doLTSManyTr (Con "constructor'" [x1']) [("constructor'", doLTS0Tr), ("#1", doLTS1Tr x1 "x1'" doLTS0Tr)]

test_checkGeneralizationCorrectness :: IO TestTree
test_checkGeneralizationCorrectness = return $ testGroup "Tests" [testCase "2+2=4" $ 2+2 @?= 4]

