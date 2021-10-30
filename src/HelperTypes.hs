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
                   

branchesForConstructor :: [(String, LTS)] -> [(String, LTS)] -> Bool
branchesForConstructor branches branches' = all (\t -> tail (map fst t) == take (length t) createLabels) [branches, branches']                   