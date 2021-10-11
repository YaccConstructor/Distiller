module LTSType (
    LTS (..), LTSTransitions (..),
    doLTS0Tr, doLTS1Tr, doLTSManyTr,
    getLabels, getOldTerm, updateLTS) where
  
import TermType

data LTS = Leaf  | LTS LTSTransitions

data LTSTransitions = LTSTransitions Term [(String, LTS)]

doLTS0Tr :: LTS
doLTS0Tr = Leaf  

doLTS1Tr :: Term -> String -> LTS -> LTS
doLTS1Tr oldTerm label newTerm = LTS $ LTSTransitions oldTerm [(label, newTerm)]

doLTSManyTr :: Term -> [(String, LTS)] -> LTS
doLTSManyTr oldTerm pairs = LTS $ LTSTransitions oldTerm pairs

updateLTS :: LTS -> String -> LTS -> String -> Term -> LTS
updateLTS lts1 label1 lts2 label2 term = doLTSManyTr term [(label1, lts1), (label2, lts2)]

getLabels :: LTSTransitions -> [String]
getLabels (LTSTransitions _ pairs) = map fst pairs

{--getNewTerms :: LTSTransitions -> [Term]
getNewTerms (LTSTransitions _ pairs) = map (\(_, y) -> 
    case y of
        (Leaf term) -> term
        (LTS (LTSTransitions tr _)) -> tr
        ) pairs --}

getOldTerm :: LTSTransitions -> Term
getOldTerm (LTSTransitions oldTerm _) = oldTerm

