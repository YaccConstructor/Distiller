module LTSType (
    LTS,
    doLTS0Tr, doLTS1Tr, doLTSManyTr,
    getLabels, getNewTerms, getOldTerm) where
  
import TermType

data LTS = Leaf Term | LTS LTSTransitions

data LTSTransitions = LTSTransitions Term [(String, LTS)]

doLTS0Tr :: Term -> LTS
doLTS0Tr = Leaf  

doLTS1Tr :: Term -> String -> LTS -> LTS
doLTS1Tr oldTerm label newTerm = LTS $ LTSTransitions oldTerm [(label, newTerm)]

doLTSManyTr :: Term -> [(String, LTS)] -> LTS
doLTSManyTr oldTerm pairs = LTS $ LTSTransitions oldTerm pairs

getLabels :: LTSTransitions -> [String]
getLabels (LTSTransitions _ pairs) = map fst pairs

getNewTerms :: LTSTransitions -> [Term]
getNewTerms (LTSTransitions _ pairs) = map (\(_, y) -> 
    case y of
        (Leaf term) -> term
        (LTS (LTSTransitions tr _)) -> tr
        ) pairs

getOldTerm :: LTSTransitions -> Term
getOldTerm (LTSTransitions oldTerm _) = oldTerm

