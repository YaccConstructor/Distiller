module Distiller (distillProg) where

import Data.Maybe (fromMaybe, mapMaybe)
import Driver
import GHC.OldList (find)
import Generalizer
import HelperTypes
import HomeomorphicEmbeddingChecker
import LTSType
import Residualizer
import TermType
import Transformer
import Unfolder
import HelperTypes
import Debug.Trace (traceShow)

distillProg :: (Term, [FunctionDefinition]) -> Term
distillProg (mainFunTerm, funDefinitions) = fst $ residualize (distill 0 (mainFunTerm, EmptyCtx) [] [] funDefinitions) funDefinitions

distill :: Int -> TermInContext -> [LTS] -> [Generalization] -> [FunctionDefinition] -> LTS
distill i t funNamesAccum p funsDefs | traceShow ("distill " ++ show i ++ ";" ++ show t) False = undefined
distill index (term@(Free x), context) funNamesAccum previousGensAccum funsDefs =
  distill' index (doLTS1Tr term (X' x) doLTS0Tr) context funNamesAccum previousGensAccum funsDefs

distill index (term@(Con conName expressions), EmptyCtx) funNamesAccum previousGensAccum funsDefs =
  let firstBranch = (Con' conName, doLTS0Tr)
      otherBranches = zip (map ConArg' createLabels) $ map (\e -> distill index (e, EmptyCtx) funNamesAccum previousGensAccum funsDefs) expressions
   in doLTSManyTr term $ (:) firstBranch otherBranches
distill index (term@(Con conName expressions), k@(ApplyCtx k' t)) _ _ _ = error $ "Constructor application is not saturated: "++show (place (Con conName expressions) (ApplyCtx k' t))
distill index (term@(Con conName expressions), k@(CaseCtx k' branches)) funNamesAccum previousGensAccum funsDefs =
  case find (\(conName', expressions', _) -> conName == conName' && length expressions' == length expressions) branches of
    Nothing -> error $ "No matching pattern in case for term:\n\n" ++ show (Case (Con conName expressions) branches)
    Just (conName', expressions', term') ->
      let oldTerm = place term k
          newTerm' = substituteTermWithNewTerms term' $ zip expressions' expressions
          newTerm = distill index (newTerm', k') funNamesAccum previousGensAccum funsDefs
       in doLTS1Tr oldTerm (UnfoldCons' conName) newTerm
distill index (term@(Lambda x expr), EmptyCtx) funNamesAccum previousGensAccum funsDefs =
  doLTS1Tr term (Lambda' x) $ distill index (expr, EmptyCtx) funNamesAccum previousGensAccum funsDefs
distill index (term@(Lambda x e0), k@(ApplyCtx k' e1)) funNamesAccum previousGensAccum funsDefs =
  doLTS1Tr (place term k) UnfoldBeta' $ distill index (substituteTermWithNewTerms e0 [(x, e1)], k') funNamesAccum previousGensAccum funsDefs
distill index termInCtx@(f@(Fun funName), k) funNamesAccum previousGensAccum funsDefs =
   let t = transform index termInCtx [] previousGensAccum funsDefs
   in case filter (null . isRenaming t) funNamesAccum of
        _ : _ -> doLTS1Tr f (Unfold' funName) doLTS0Tr
        [] -> case mapMaybe ( \t' -> case isHomeomorphicEmbedding t t' of
                            [] -> Nothing
                            renaming -> Just (renaming, t')) funNamesAccum of
          (_, t') : _ ->
            let generalizedLTS = generalize t t' previousGensAccum
                residualizedLTS = residualize generalizedLTS
             in error "error1" --distill (index + 1) (unfold residualizedLTS funsDefs, EmptyCtx) [generalizedLTS] previousGensAccum []
          [] ->
            let oldTerm = place f k
                residualized = residualize t funsDefs
                newTerm = distill index (unfold (fst $ residualized) funsDefs, EmptyCtx) (t : funNamesAccum) previousGensAccum funsDefs
             in doLTS1Tr oldTerm (Unfold' funName) newTerm
distill index (Apply e0 e1, k) funNamesAccum previousGensAccum funsDefs =
  distill index (e0, ApplyCtx k e1) funNamesAccum previousGensAccum funsDefs
distill index (Case e0 branches, k) funNamesAccum previousGensAccum funsDefs =
  distill index (e0, CaseCtx k branches) funNamesAccum previousGensAccum funsDefs
distill index (e@(Let x e0 e1), k) funNamesAccum previousGensAccum funsDefs =
  let firstBranch = (Let', distill index (substituteTermWithNewTerms e1 [(x, e0)], k) funNamesAccum previousGensAccum funsDefs)
      secondBranch = (LetX' x, distill index (e0, EmptyCtx) funNamesAccum previousGensAccum funsDefs)
   in doLTSManyTr (place e k) [firstBranch, secondBranch]
distill index (MultipleApply e0 funsDefs', context) funNamesAccum previousGensAccum funsDefs =
  let
   in distill index (e0, context) funNamesAccum previousGensAccum $ funsDefs ++ funsDefs'
distill index e _ _ _ | traceShow ("Nothing matched " ++ show e) False = undefined
distill index e _ _ _ = error $ "Nothing matched with " ++ show e ++ show " distillation."

distill' :: Int -> LTS -> Context -> [LTS] -> [Generalization] -> [FunctionDefinition] -> LTS
distill' _ lts EmptyCtx _ _ _ = lts
distill' index t@(LTS lts) (ApplyCtx context expr) funNames previousGensAccum funsDefs =
  let term = getOldTerm lts
      newLts = updateLTS t Apply0' (distill index (expr, EmptyCtx) funNames previousGensAccum funsDefs) Apply1' (Apply term expr)
   in distill' index newLts context funNames previousGensAccum funsDefs
distill' index t@(LTS lts) (CaseCtx context branches) funsNames previousGens funsDefs =
  let root = Case (getOldTerm lts) branches
      firstBranch = (Case', t)
      otherBranches = map (\(branchName, args, resultTerm) ->
        (CaseBranch' branchName args, distill index (place resultTerm context, EmptyCtx) funsNames previousGens funsDefs)) branches
   in doLTSManyTr root $ firstBranch : otherBranches
distill' index t@(LTS (LTSTransitions term@(Free x) [(X' x', _)])) (CaseCtx context branches) funsNames previousGens funsDefs =
  if x == x'
    then
      let root = Case term branches
          firstBranch = (Case', t)
          otherBranches =
            map
              ( \(branchName, args, resultTerm) ->
                  if length args > 1
                    then error "Got one free variable, but pattern matching uses more."
                    else
                      let resultTerm' = substituteTermWithNewVars resultTerm [(head args, x')]
                          distilledTerm = distill index (place resultTerm' context, EmptyCtx) funsNames previousGens funsDefs
                       in (CaseBranch' branchName args, distilledTerm)
              )
              branches
       in doLTSManyTr root $ firstBranch : otherBranches
    else error "Error: got branch x -> (x,0), but label is not the same as x"
distill' _ _ _ _ _ _ = error "Got error during execution distill'."