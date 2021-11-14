module Residualizer (residualize) where
  
import TermType
import LTSType
import HelperTypes  
  
residualize :: LTS -> Term
residualize lts = Free "x"
  
  
