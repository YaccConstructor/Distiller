module Distiller (distill) where

import LTSType 
import TermType
import HelperTypes

distill :: LTS -> Context -> [LTS] -> [Generalization] -> [FunctionDefinition] -> LTS
distill = dN

dN :: LTS -> Context -> [LTS] -> [Generalization] -> [FunctionDefinition] -> LTS
dN lts context funCallsAccum previousGensAccum funsDefs = lts