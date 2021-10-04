module Distiller (distill) where

import LTSType 
import TermType
import HelperTypes

distill :: Term -> Context -> [String] -> [Generalization] -> [FunctionDefinition] -> LTS
distill = dN

dN :: Term -> Context -> [String] -> [Generalization] -> [FunctionDefinition] -> LTS
dN term context funNamesAccum previousGensAccum funsDefs = doLTS0Tr term