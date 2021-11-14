module HelperTypes where

import TermType
import LTSType
import Data.Maybe (fromMaybe)

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

-- concrete function alternative
substituteTermWithNewVars :: Term -> [(String, String)] -> Term
substituteTermWithNewVars (Free x) pairs = case lookup x pairs of
  Nothing -> Free x
  Just x' -> Free x'
substituteTermWithNewVars (Lambda x expr) xs = Lambda ("\\" ++ x) $ substituteTermWithNewVars expr xs
substituteTermWithNewVars (Apply term1 term2) xs =
  let term1' = substituteTermWithNewVars term1 xs
      term2' = substituteTermWithNewVars term2 xs
   in Apply term1' term2'
substituteTermWithNewVars (Case term branches) xs =
  let term' = substituteTermWithNewVars term xs
      branches' = map (\(cons, vars, branchTerm) -> (cons, vars, substituteTermWithNewVars branchTerm xs)) branches
   in Case term' branches'
substituteTermWithNewVars (Let x term1 term2) xs =
  let term1' = substituteTermWithNewVars term1 xs
      term2' = substituteTermWithNewVars term2 xs
   in Let x term1' term2'
substituteTermWithNewVars (Con constructorName terms) xs =
  let terms' = map (`substituteTermWithNewVars` xs) terms
   in Con constructorName terms'
substituteTermWithNewVars (MultipleApply e0 funsDefs) xs =
  let e0' = substituteTermWithNewVars e0 xs
      funsDefs' =
        map
          ( \(funName, (args, term)) ->
              let renamedArgs = map (\t -> fromMaybe t (lookup t xs)) args
               in (funName, (renamedArgs, substituteTermWithNewVars term xs))
          )
          funsDefs
   in MultipleApply e0' funsDefs'
substituteTermWithNewVars fun _ = fun

substituteTermWithNewTerms :: Term -> [(String, Term)] -> Term
substituteTermWithNewTerms term _ = term