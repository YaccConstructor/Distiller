module Transformer (transform) where

import Data.Maybe (fromMaybe, mapMaybe)
import Driver
import GHC.OldList (find)
import Generalizer
import HelperTypes
import HomeomorphicEmbeddingChecker
import LTSType
import Residualizer
import TermType
import Unfolder

-- concrete function alternative
substituteTermWithNewVars :: Term -> [(String, String)] -> Term
substituteTermWithNewVars (Free x) pairs = case lookup x pairs of
  Nothing -> Free x
  Just x' -> Free x'
substituteTermWithNewVars (Lambda x expr) xs = Lambda x $ substituteTermWithNewVars expr xs
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

transform :: Int -> TermInContext -> [LTS] -> [Generalization] -> [FunctionDefinition] -> LTS
transform index (term@(Free x), context) funNamesAccum previousGensAccum funsDefs =
  transform' index (doLTS1Tr term x doLTS0Tr) context funNamesAccum previousGensAccum funsDefs
transform index (term@(Con conName expressions), EmptyCtx) funNamesAccum previousGensAccum funsDefs =
  let firstBranch = (conName, doLTS0Tr)
      otherBranches = zip createLabels $ map (\e -> transform index (e, EmptyCtx) funNamesAccum previousGensAccum funsDefs) expressions
   in doLTSManyTr term $ (:) firstBranch otherBranches
transform index (term@(Con conName expressions), k@(CaseCtx k' branches)) funNamesAccum previousGensAccum funsDefs =
  case find (\(conName', expressions', _) -> conName == conName' && length expressions' == length expressions) branches of
    Nothing -> error $ "No matching pattern in case for term:\n\n" ++ show (Case (Con conName expressions) branches)
    Just (conName', expressions', term') ->
      let oldTerm = place term k
          newTerm' = substituteTermWithNewTerms term' $ zip expressions' expressions
          newTerm = transform index (newTerm', k') funNamesAccum previousGensAccum funsDefs
       in doLTS1Tr oldTerm conName' newTerm
transform index (term@(Lambda x expr), EmptyCtx) funNamesAccum previousGensAccum funsDefs =
  doLTS1Tr term x $ transform index (expr, EmptyCtx) funNamesAccum previousGensAccum funsDefs
transform index (term@(Lambda x e0), k@(ApplyCtx k' e1)) funNamesAccum previousGensAccum funsDefs =
  doLTS1Tr (place term k) "beta" $ transform index (substituteTermWithNewTerms e0 [(x, e1)], k') funNamesAccum previousGensAccum funsDefs
transform index termInCtx@(f@(Fun funName), k) funNamesAccum previousGensAccum funsDefs =
  let t =
        if index == 0
          then drive (place f k) [] funsDefs
          else transform (index - 1) termInCtx [] previousGensAccum funsDefs
   in case filter (null . isRenaming t) funNamesAccum of
        _ : _ -> doLTS1Tr f funName doLTS0Tr
        [] -> case mapMaybe
          ( \t' -> case isHomeomorphicEmbedding t t' of
              [] -> Nothing
              renaming -> Just (renaming, t')
          )
          funNamesAccum of
          (_, t') : _ ->
            let generalizedLTS = generalize t t' previousGensAccum
                residualizedLTS = residualize generalizedLTS
             in transform index (residualizedLTS, EmptyCtx) funNamesAccum previousGensAccum []
          [] ->
            let oldTerm = place f k
                newTerm = transform index (unfold oldTerm funsDefs, EmptyCtx) (t : funNamesAccum) previousGensAccum funsDefs
             in doLTS1Tr oldTerm funName newTerm
transform index (Apply e0 e1, k) funNamesAccum previousGensAccum funsDefs =
  transform index (e0, ApplyCtx k e1) funNamesAccum previousGensAccum funsDefs
transform index (Case e0 branches, k) funNamesAccum previousGensAccum funsDefs =
  transform index (e0, CaseCtx k branches) funNamesAccum previousGensAccum funsDefs
transform index (e@(Let x e0 e1), k) funNamesAccum previousGensAccum funsDefs =
  let firstBranch = ("let", transform index (substituteTermWithNewTerms e1 [(x, e0)], k) funNamesAccum previousGensAccum funsDefs)
      secondBranch = (x, transform index (e0, EmptyCtx) funNamesAccum previousGensAccum funsDefs)
   in doLTSManyTr (place e k) [firstBranch, secondBranch]
transform index (MultipleApply e0 funsDefs', context) funNamesAccum previousGensAccum funsDefs =
  let
   in transform index (e0, context) funNamesAccum previousGensAccum $ funsDefs ++ funsDefs'
transform _ _ _ _ _ = error "Got error during execution transform."

transform' :: Int -> LTS -> Context -> [LTS] -> [Generalization] -> [FunctionDefinition] -> LTS
transform' _ lts EmptyCtx _ _ _ = lts
transform' index t@(LTS lts) (ApplyCtx context expr) funNames previousGensAccum funsDefs =
  let term = getOldTerm lts
      newLts = updateLTS t "@" (transform index (expr, EmptyCtx) funNames previousGensAccum funsDefs) "#1" (Apply term expr)
   in transform' index newLts context funNames previousGensAccum funsDefs
transform' index t@(LTS lts) (CaseCtx context branches) funsNames previousGens funsDefs =
  let root = Case (getOldTerm lts) branches
      firstBranch = ("case", t)
      otherBranches = map (\(branchName, _, resultTerm) -> (branchName, transform index (resultTerm, context) funsNames previousGens funsDefs)) branches
   in doLTSManyTr root $ firstBranch : otherBranches
transform' index t@(LTS (LTSTransitions term@(Free x) [(xLabel, _)])) (CaseCtx context branches) funsNames previousGens funsDefs =
  if x == xLabel
    then
      let root = Case term branches
          firstBranch = ("case", t)
          otherBranches =
            map
              ( \(branchName, args, resultTerm) ->
                  if length args > 1
                    then error "Got one free variable, but pattern matching uses more."
                    else
                      let resultTerm' = substituteTermWithNewVars resultTerm [(head args, xLabel)]
                          transformedTerm = transform index (resultTerm', context) funsNames previousGens funsDefs
                       in (branchName, transformedTerm)
              )
              branches
       in doLTSManyTr root $ firstBranch : otherBranches
    else error "Error: got branch x -> (x,0), but label is not the same as x"
transform' _ _ _ _ _ _ = error "Got error during execution transform'."
