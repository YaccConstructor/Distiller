module HelperTypes where

import TermType
import LTSType

type FunctionDefinition = (String, ([String], Term))
type Generalization = (Term, LTS)

type Prog = (Term,[(String,([String],Term))])

createLabels :: [String]
createLabels = map ((++) "#" . show) [1 ..]