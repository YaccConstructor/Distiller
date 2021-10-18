module Unfolder (unfold) where

import HelperTypes  
import TermType
    
unfold :: Term -> [FunctionDefinition] -> Term  
unfold term funsDefs = term 

