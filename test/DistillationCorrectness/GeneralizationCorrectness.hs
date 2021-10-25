module GeneralizationCorrectness where

import Generalizer
import LTSType
import TermType
import Test.Tasty.HUnit


lts1 = doLTSManyTr (Con "constructor" [x1@(Free "x1")]) [("constructor", doLTS0Tr), ("#1", doLTS1Tr x1 "x1" doLTS0Tr)]
lts2 = doLTSManyTr (Con "constructor'" [(Free "x1'")]) [("constructor'", doLTS0Tr), ("#1", doLTS1Tr x1 "x1'" doLTS0Tr)]

checkGeneralizationCorrectness = generalize lts1 lts2 [] == doLTSTr0

