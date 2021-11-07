module DistillationCorrectness.GeneralizationCorrectness where

import Generalizer
import LTSType
import TermType
import Test.Tasty
import Test.Tasty.HUnit

x1 = Free "x1"
lts1 = doLTSManyTr (Con "S" [Con "S" [Free "Z"]])
                    [(Con' "S", doLTS0Tr)
                    ,(ConArg' "#1", doLTSManyTr (Con "S" [Free "Z"]) [(Con' "S", doLTS0Tr), (ConArg' "#1", doLTS1Tr (Free "Z") (X' "Z") doLTS0Tr)])
                    ]

lts2 = doLTSManyTr (Con "S" [Free "Z"]) [(Con' "S", doLTS0Tr), (ConArg' "#1", doLTS1Tr (Free "Z") (X' "Z") doLTS0Tr)]

resultLts = doLTSManyTr (Con "S" [Con "S" [Free "Z"]])
            [(Let', doLTSManyTr (Con "S" [Con "S" [Free "Z"]])
                    [(Con' "S", doLTS0Tr),(ConArg' "#1", doLTS1Tr (Free "x") (X' "x") doLTS0Tr)])
            ,(LetX' "x", doLTSManyTr (Con "S" [Con "S" [Free "Z"]])
                    [(Con' "S", doLTS0Tr), (ConArg' "#1", doLTS1Tr (Free "Z") (X' "Z")  doLTS0Tr)])]

test_checkGeneralizationCorrectness :: IO TestTree
test_checkGeneralizationCorrectness = return $ testGroup "Tests" [testCase "let x1 = S Z in let x2 = S S Z" $ generalize lts1 lts2 [] @?= resultLts]

