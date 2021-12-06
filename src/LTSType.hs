module LTSType (
    LTS (..), LTSTransitions (..), LTSTransitions (..), Label (..),
    doLTS0Tr, doLTS1Tr, doLTSManyTr,
    getLabels, getOldTerm, updateLTS) where
  
import TermType

data LTS = Leaf  | LTS LTSTransitions deriving Show

data LTSTransitions = LTSTransitions Term [(Label, LTS)] deriving (Show)

data Label = Con' String
           | ConArg' String
           | X' String
           | Lambda' String
           | Unfold' String
           | UnfoldBeta'
           | UnfoldCons' String
           | Case'
           | CaseBranch' String [String]
           | Let'
           | LetX' String
           | Apply0'
           | Apply1' deriving (Eq, Show, Ord)

instance Eq LTS where
  (==) Leaf Leaf = True
  (==) (LTS (LTSTransitions _ _)) Leaf = False
  (==) Leaf (LTS (LTSTransitions _ _)) = False
  (==) (LTS (LTSTransitions term branches)) (LTS (LTSTransitions term' branches')) = 
    length branches == length branches' && (let
    termsEq = term == term'
    labelsEq = all (\(l, l') -> l == l') $ zip (map fst branches) (map fst branches')
    terms'Eq = all (\(t, t') -> t == t') $ zip (map snd branches) (map snd branches')
    result = termsEq && labelsEq && terms'Eq 
    in result)

instance Ord LTS where
  (>) (LTS (LTSTransitions _ _)) Leaf = True
  (>) Leaf (LTS (LTSTransitions _ _)) = False
  (>) (LTS (LTSTransitions term branches)) (LTS (LTSTransitions term' branches'))
    | length branches > length branches' = True
    | length branches < length branches' = False
    | term < term' = False
    | otherwise = all (\((label, lts), (label', lts')) -> label > label' && lts > lts') (zip branches branches')


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

