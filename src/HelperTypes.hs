module HelperTypes where

import TermType
import LTSType

type FunctionDefinition = (String, ([String], Term))
type Generalization = (Term, LTS)

type Prog = (Term,[(String,([String],Term))])

createLabels :: [String]
createLabels = map ((++) "#" . show) [1 ..]

renameVar fv x = if   x `elem` fv
                 then renameVar fv (x++"'")
                 else x
renameVars fv xs = foldr (\x fv -> let x' = renameVar fv x in x':fv) fv xs                 

branchesForConstructor :: [(Label, LTS)] -> [(Label, LTS)] -> Bool
branchesForConstructor branches branches' = all (\t -> tail (map fst t) == take (length t - 1) (map ConArg' createLabels)) [branches, branches']     

--matchCase :: (Eq a1, Foldable t1, Foldable t2) => [(a1, t1 a2, c1)] -> [(a1, t2 a3, c2)] -> Bool
--matchCase bs bs' = length bs == length bs' && all (\((c,xs,_),(c',xs',_)) -> c == c' && length xs == length xs') (zip bs bs')
matchCase bs bs' = True