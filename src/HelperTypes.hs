module HelperTypes where

import TermType

type FunctionDefinition = (String, [(String, Term)])
type Generalization = (Term, Term)
type Prog = (Term,[(String,([String],Term))])