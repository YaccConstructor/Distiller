module Driver where

import TermType
import LTSType
import HelperTypes

drive :: Prog -> LTS
drive _ = doLTS0Tr $ Free "t"