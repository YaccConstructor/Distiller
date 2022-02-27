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
import HelperTypes
import Debug.Trace (traceShow, trace)

transform :: Int -> TermInContext -> [LTS] -> [Generalization] -> [FunctionDefinition] -> LTS
--transform n t f p funsDefs | traceShow ("transform" ++ show n ++ show t ++ show f ++ show p ++ show funsDefs) False = undefined
transform index (term@(Free x), context) funNamesAccum previousGensAccum funsDefs =
  transform' index (doLTS1Tr term (X' x) doLTS0Tr) context funNamesAccum previousGensAccum funsDefs
   
transform index (term@(Con conName expressions), EmptyCtx) funNamesAccum previousGensAccum funsDefs =
  let firstBranch = (Con' conName, doLTS0Tr)
      otherBranches = zip (map ConArg' createLabels) $ map (\e -> transform index (e, EmptyCtx) funNamesAccum previousGensAccum funsDefs) expressions
   in doLTSManyTr term $ (:) firstBranch otherBranches
transform index (term@(Con conName expressions), k@(CaseCtx k' branches)) funNamesAccum previousGensAccum funsDefs =
  case find (\(conName', expressions', _) -> conName == conName' && length expressions' == length expressions) branches of
    Nothing -> error $ "No matching pattern in case for term:\n\n" ++ show (Case (Con conName expressions) branches)
    Just (conName', expressions', term') ->
      let oldTerm = place term k
          newTerm' = substituteTermWithNewTerms term' $ zip expressions' expressions
          newTerm = transform index (newTerm', k') funNamesAccum previousGensAccum funsDefs
       in doLTS1Tr oldTerm (UnfoldCons' conName) newTerm       
transform index (term@(Lambda x expr), EmptyCtx) funNamesAccum previousGensAccum funsDefs =
  doLTS1Tr term (Lambda' x) $ transform index (expr, EmptyCtx) funNamesAccum previousGensAccum funsDefs
transform index (term@(Lambda x e0), k@(ApplyCtx k' e1)) funNamesAccum previousGensAccum funsDefs | traceShow ("lambda: " ++ show ((substituteTermWithNewTerms e0 [(x, e1)], k'))) False = undefined
transform index (term@(Lambda x e0), k@(ApplyCtx k' e1)) funNamesAccum previousGensAccum funsDefs =
  doLTS1Tr (place term k) UnfoldBeta' $ transform index (substituteTermWithNewTerms e0 [(x, e1)], k') funNamesAccum previousGensAccum funsDefs
transform index termInCtx@(f@(Fun funName), k) funNamesAccum previousGensAccum funsDefs | traceShow ("index = " ++ show index ++ show (if index == 0
                                                                                                then drive (place f k) [] funsDefs
                                                                                                else transform (index - 1) termInCtx [] previousGensAccum funsDefs)) False = undefined
transform index termInCtx@(f@(Fun funName), k) funNamesAccum previousGensAccum funsDefs =
   let t =
        if index == 0
          then drive (place f k) [] funsDefs
          else transform (index - 1) termInCtx [] previousGensAccum funsDefs
   in do {
     case filter (not . null . isRenaming t) funNamesAccum of
        _ : _ -> do {
          --traceShow ("renaming passed##")
          doLTS1Tr (place f k) (Unfold' funName) doLTS0Tr
          }
        [] -> case mapMaybe
          ( \t' -> case isHomeomorphicEmbedding t t' of
              [] -> Nothing
              renaming -> Just (renaming, t')
          )
          funNamesAccum of
          (_, t') : _ ->
            let generalizedLTS = generalize t t' previousGensAccum
                residualizedLTS = residualize generalizedLTS funsDefs
             in do {
               --trace ("before gen t = " ++ show t ++ "; funNamesAccum = " ++ show funNamesAccum)
               error "error"
               --transform index (fst residualizedLTS, EmptyCtx) funNamesAccum previousGensAccum []
               }
          [] ->
            let oldTerm = place f k
                newTerm = if (index == 0)
                    then transform index (unfold oldTerm funsDefs, EmptyCtx) (t : funNamesAccum) previousGensAccum funsDefs
                    else let
                        residualized = residualize t funsDefs
                        result = transform index (unfold (fst residualized) funsDefs, EmptyCtx) (t : funNamesAccum) previousGensAccum (funsDefs ++ snd residualized)
                        in do {
                          trace ("Residualized!! n = " ++ show index ++ "t = " ++ show t 
                            ++ "; residualized = " ++ show residualized 
                            ++ "; unfold =" ++ show (unfold (fst residualized) funsDefs) 
                            ++ "; result = " ++ show result)
                          result
                          }
             in do {
               doLTS1Tr oldTerm (Unfold' funName) newTerm
               }
               }
transform index (term@(Apply e0 e1), k) funNamesAccum previousGensAccum funsDefs =
  let term' = doBetaReductions term in
  if term' == term
    then transform index (e0, ApplyCtx k e1) funNamesAccum previousGensAccum funsDefs
    else transform index (term', k) funNamesAccum previousGensAccum funsDefs
transform index (Case e0 branches, k) funNamesAccum previousGensAccum funsDefs =
  transform index (e0, CaseCtx k branches) funNamesAccum previousGensAccum funsDefs
transform index (e@(Let x e0 e1), k) funNamesAccum previousGensAccum funsDefs =
  let firstBranch = (Let', transform index (substituteTermWithNewTerms e1 [(x, e0)], k) funNamesAccum previousGensAccum funsDefs)
      secondBranch = (LetX' x, transform index (e0, EmptyCtx) funNamesAccum previousGensAccum funsDefs)
   in doLTSManyTr (place e k) [firstBranch, secondBranch]
transform index (MultipleApply e0 funsDefs', context) funNamesAccum previousGensAccum funsDefs =
  let
   in transform index (e0, context) funNamesAccum previousGensAccum $ funsDefs ++ funsDefs'
transform _ (e0, context) _ _ _ = error $ "Nothing matched for " ++ show e0 ++ show context ++ " during transform."

transform' :: Int -> LTS -> Context -> [LTS] -> [Generalization] -> [FunctionDefinition] -> LTS
transform' _ lts EmptyCtx _ _ _ = lts
transform' index t@(LTS lts) (ApplyCtx context expr) _ _ _ | traceShow ("in transform': lts = " ++ show lts ++ "; ctx = " ++ show context ++ "; expr = " ++ show expr) False = undefined
transform' index t@(LTS lts) (ApplyCtx context expr) funNames previousGensAccum funsDefs =
  let term = getOldTerm lts
      newLts = updateLTS t Apply0' (transform index (expr, EmptyCtx) funNames previousGensAccum funsDefs) Apply1' (Apply term expr)
   in transform' index newLts context funNames previousGensAccum funsDefs
transform' index t@(LTS (LTSTransitions term@(Free x) [(X' x', _)])) (CaseCtx context branches) funsNames previousGens funsDefs 
    | traceShow ("In transform, want to substitute branches in case " ++ show branches ++ "; with " ++ show x' ++ "") False = undefined
transform' index t@(LTS (LTSTransitions term@(Free x) [(X' x', _)])) (CaseCtx context branches) funsNames previousGens funsDefs =
  if x == x'
    then
      let root = Case term branches
          firstBranch = (Case', t)
          otherBranches =
            map
              ( \(branchName, args, resultTerm) -> let
                          resultTerm'' = substituteTermWithNewTerms resultTerm [(x', Con branchName $ map Free args)]
                          transformedTerm = transform index (resultTerm'', context) funsNames previousGens funsDefs
                       in (CaseBranch' branchName args, transformedTerm)
              )
              branches
       in do { 
       doLTSManyTr root $ firstBranch : otherBranches
       }
    else error "Error: got branch x -> (x,0), but label is not the same as x"
transform' index t@(LTS lts) (CaseCtx context branches) funsNames previousGens funsDefs =
  let root = Case (getOldTerm lts) branches
      firstBranch = (Case', t)
      otherBranches = map (\(branchName, args, resultTerm) ->
        (CaseBranch' branchName args, transform index (resultTerm, context) funsNames previousGens funsDefs)) branches
   in doLTSManyTr root $ firstBranch : otherBranches
transform' _ _ _ _ _ _ = error "Got error during execution transform'."
