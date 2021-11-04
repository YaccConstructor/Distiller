module LTSType (
    LTS (..), LTSTransitions (..), LTSTransitions (..), Label (..),
    doLTS0Tr, doLTS1Tr, doLTSManyTr,
    getLabels, getOldTerm, updateLTS) where
  
import TermType

data LTS = Leaf  | LTS LTSTransitions

data LTSTransitions = LTSTransitions Term [(Label, LTS)]

data Label = Con' String
           | ConArg' String
           | Lambda' String
           | Unfold' String
           | Case'
           | CaseBranch' String [String]
           | Let'
           | LetX' String
           | Apply0'
           | Apply1' deriving Eq


instance Eq LTS where
  (==) Leaf Leaf = True
  (==) _ _ = error "Not defined."


doLTS0Tr :: LTS
doLTS0Tr = Leaf  

doLTS1Tr :: Term -> Label -> LTS -> LTS
doLTS1Tr oldTerm label newTerm = LTS $ LTSTransitions oldTerm [(label, newTerm)]

doLTSManyTr :: Term -> [(Label, LTS)] -> LTS
doLTSManyTr oldTerm pairs = LTS $ LTSTransitions oldTerm pairs

updateLTS :: LTS -> Label -> LTS -> Label -> Term -> LTS
updateLTS lts1 label1 lts2 label2 term = doLTSManyTr term [(label1, lts1), (label2, lts2)]

getLabels :: LTSTransitions -> [Label]
getLabels (LTSTransitions _ pairs) = map fst pairs

{--getNewTerms :: LTSTransitions -> [Term]
getNewTerms (LTSTransitions _ pairs) = map (\(_, y) -> 
    case y of
        (Leaf term) -> term
        (LTS (LTSTransitions tr _)) -> tr
        ) pairs --}

getOldTerm :: LTSTransitions -> Term
getOldTerm (LTSTransitions oldTerm _) = oldTerm

