module Distiller (distill) where

import LTSType 
import TermType


distill :: Term -> Context -> [String] -> [(Term, Term)] -> p4 -> LTS
distill = d_n

d_n :: Term -> Context -> [String] -> [(Term, Term)] -> p4 -> LTS
d_n term context funNamesAccum previousGensAccum funsDefs = doLTS0Tr term