module Distiller (distillProg) where

import Data.Maybe (fromMaybe, mapMaybe)
import Driver
import GHC.OldList (find, nub)
import Generalizer
import HelperTypes
import HomeomorphicEmbeddingChecker
import LTSType
import Residualizer
import TermType
import Transformer
import Unfolder
import HelperTypes
import Debug.Trace (traceShow, trace)

distillProg :: (Term, [FunctionDefinition]) -> Term
distillProg (mainFunTerm, funDefinitions) = let
    (funsDefs', prog) = distill 2 (mainFunTerm, EmptyCtx) [] [] funDefinitions

    in do {
      traceShow ("prog = " ++ show (funsDefs', prog) ++ "; residualized prog = " ++ show (residualize prog funsDefs'))
      fst $ residualize prog funsDefs'
      --(Fun "f") -- ++ show (fst result) ++ show (snd result))
    }

distill :: Int -> TermInContext -> [LTS] -> [Generalization] -> [FunctionDefinition] -> ([FunctionDefinition], LTS)
--distill i t funNamesAccum p funsDefs | traceShow ("distill " ++ show i ++ ";" ++ show t) False = undefined
distill index (term@(Free x), context) funNamesAccum previousGensAccum funsDefs =
  distill' index (doLTS1Tr term (X' x) doLTS0Tr) context funNamesAccum previousGensAccum funsDefs

distill index (term@(Con conName expressions), EmptyCtx) funNamesAccum previousGensAccum funsDefs = let
      firstBranch = (Con' conName, doLTS0Tr)
      distilledBranches = map (\e -> distill index (e, EmptyCtx) funNamesAccum previousGensAccum funsDefs) expressions
      funsDefs' = nub $ concatMap fst distilledBranches
      otherBranches = zip (map ConArg' createLabels) $ map snd distilledBranches
   in (nub $ funsDefs' ++ funsDefs, doLTSManyTr term $ (:) firstBranch otherBranches)
distill index (term@(Con conName expressions), k@(ApplyCtx k' t)) _ _ _ = error $ "Constructor application is not saturated: "++show (place (Con conName expressions) (ApplyCtx k' t))
distill index (term@(Con conName expressions), k@(CaseCtx k' branches)) funNamesAccum previousGensAccum funsDefs =
  case find (\(conName', expressions', _) -> conName == conName' && length expressions' == length expressions) branches of
    Nothing -> error $ "No matching pattern in case for term:\n\n" ++ show (Case (Con conName expressions) branches)
    Just (conName', expressions', term') -> let
          oldTerm = place term k
          newTerm' = substituteTermWithNewTerms term' $ zip expressions' expressions
          (funsDefs', newTerm) = distill index (newTerm', k') funNamesAccum previousGensAccum funsDefs
       in (nub $ funsDefs' ++ funsDefs, doLTS1Tr oldTerm (UnfoldCons' conName) newTerm)
distill index (term@(Lambda x expr), EmptyCtx) funNamesAccum previousGensAccum funsDefs = let
    (funsDefs', term') = distill index (expr, EmptyCtx) funNamesAccum previousGensAccum funsDefs
  in (nub $ funsDefs' ++ funsDefs, doLTS1Tr term (Lambda' x) term')
distill index (term@(Lambda x e0), k@(ApplyCtx k' e1)) funNamesAccum previousGensAccum funsDefs = let
    (funsDefs', term') = distill index (substituteTermWithNewTerms e0 [(x, e1)], k') funNamesAccum previousGensAccum funsDefs
  in (nub $ funsDefs' ++ funsDefs, doLTS1Tr (place term k) UnfoldBeta' term')
distill index termInCtx@(f@(Fun funName), k) funNamesAccum previousGensAccum funsDefs | traceShow ("distill index = " ++ show index
    ++ "funsDefs = " ++ show (nub funsDefs)
    ++ "t = " ++ show (snd $ transform index termInCtx [] previousGensAccum funsDefs)
    ++ "isRenaming t t'' = " ++ show (isRenaming (snd $ transform index termInCtx [] previousGensAccum funsDefs) (LTS (LTSTransitions (Apply (Apply (Fun "f") (Free "xs")) (Free "ys")) [(Unfold' "f",LTS (LTSTransitions
                                                                                                                                 (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs#"],Apply (Apply (Fun "f") (Free "xs#")) (Free "ys"))]) [(Case',LTS (LTSTransitions (Free "xs")
                                                                                                                                 [(X' "xs",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)])),(CaseBranch' "Cons" ["x","xs#"],LTS (LTSTransitions (Apply (Apply (Fun "f")
                                                                                                                                 (Free "xs#")) (Free "ys")) [(Unfold' "f",Leaf)]))]))])))) False = undefined
distill index termInCtx@(f@(Fun funName), k) funNamesAccum previousGensAccum funsDefs =
   let (funsDefs', t) = transform index termInCtx [] previousGensAccum funsDefs
       {---t'' = LTS (LTSTransitions (Apply (Apply (Fun "f") (Free "xs")) (Free "ys")) [(Unfold' "f",LTS (LTSTransitions
               (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs#"],Apply (Apply (Fun "f") (Free "xs#")) (Free "ys"))]) [(Case',LTS (LTSTransitions (Free "xs")
               [(X' "xs",Leaf)])),(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)])),(CaseBranch' "Cons" ["x","xs#"],LTS (LTSTransitions (Apply (Apply (Fun "f")
               (Free "xs#")) (Free "ys")) [(Unfold' "f",Leaf)]))]))])--}
   in case filter (not . null . isRenaming t) (funNamesAccum) of
        _ : _ -> (funsDefs', doLTS1Tr (place f k) (Unfold' funName) doLTS0Tr)
        [] -> case mapMaybe ( \t' -> case isHomeomorphicEmbedding t t' of
                            [] -> Nothing
                            renaming -> Just (renaming, t')) funNamesAccum of
          (_, t') : _ ->
            let generalizedLTS = generalize t t' previousGensAccum
                residualizedLTS = residualize generalizedLTS
             in error "error1" --distill (index + 1) (unfold residualizedLTS funsDefs, EmptyCtx) [generalizedLTS] previousGensAccum []
          [] ->
            let oldTerm = place f k
                (residualized, funsDefs'') = residualize t funsDefs'
                (funsDefs''', newTerm) = distill index (unfold (residualized) funsDefs', EmptyCtx) (t : funNamesAccum) previousGensAccum (nub $ funsDefs' ++ funsDefs'' ++ funsDefs)
             in do {
                --traceShow ("Residualized in distill: " ++ show index ++ "; t = " ++ show t)-- ++ ";  residualized =" ++ show residualized ++ "; funNamesAccum = " ++ show funNamesAccum) -- ++ show newTerm)
                case filter (\(_, (_, fundef)) -> not $ null $ concat $ termRenaming fundef oldTerm) funsDefs' of
                                                         (funname, (vars, fundef)) : _ -> let
                                                           renamings = concat $ termRenaming fundef oldTerm
                                                           vars' = map (\var -> case lookup var renamings of
                                                                                   Nothing -> Free var
                                                                                   Just var' -> var') vars
                                                           oldTerm' = foldl (Apply) (Fun funname) vars'
                                                           in do {
                                                           --traceShow ("renaming passed!" ++ show t ++ ";;" ++ show e ++ ";" ++ show vars ++ "; result = " ++ show (foldl (Apply) (Fun funname) (vars')))
                                                              (funsDefs''', doLTS1Tr oldTerm' (Unfold' funname) newTerm)
                                                           }
                                                         _ -> (funsDefs''', doLTS1Tr oldTerm (Unfold' funName) newTerm)
                }
distill index (term@(Apply e0 e1), k) funNamesAccum previousGensAccum funsDefs =
  let term' = doBetaReductions term in
  if term' == term
    then distill index (e0, ApplyCtx k e1) funNamesAccum previousGensAccum funsDefs
    else distill index (term', k) funNamesAccum previousGensAccum funsDefs
distill index (Case e0 branches, k) funNamesAccum previousGensAccum funsDefs =
  distill index (e0, CaseCtx k branches) funNamesAccum previousGensAccum funsDefs
distill index (e@(Let x e0 e1), k) funNamesAccum previousGensAccum funsDefs =
  let (funsDefs', firstBranchDistilled) = distill index (substituteTermWithNewTerms e1 [(x, e0)], k) funNamesAccum previousGensAccum funsDefs
      firstBranch = (Let', firstBranchDistilled)
      (funsDefs'', secondBranchDistilled) = distill index (e0, EmptyCtx) funNamesAccum previousGensAccum funsDefs
      secondBranch = (LetX' x, secondBranchDistilled)
   in (nub $ funsDefs' ++ funsDefs'' ++ funsDefs, doLTSManyTr (place e k) [firstBranch, secondBranch])
distill index (MultipleApply e0 funsDefs', context) funNamesAccum previousGensAccum funsDefs =
  let
   in distill index (e0, context) funNamesAccum previousGensAccum $ funsDefs ++ funsDefs'
distill index e _ _ _ | traceShow ("Nothing matched " ++ show e) False = undefined
distill index e _ _ _ = error $ "Nothing matched with " ++ show e ++ show " distillation."

distill' :: Int -> LTS -> Context -> [LTS] -> [Generalization] -> [FunctionDefinition] -> ([FunctionDefinition], LTS)
distill' _ lts EmptyCtx _ _ funsDefs = (funsDefs, lts)
distill' index t@(LTS lts) (ApplyCtx context expr) funNames previousGensAccum funsDefs =
  let term = getOldTerm lts
      (funsDefs', newTerm) = distill index (expr, EmptyCtx) funNames previousGensAccum funsDefs
      newLts = updateLTS t Apply0' newTerm Apply1' (Apply term expr)
   in distill' index newLts context funNames previousGensAccum (nub $ funsDefs ++ funsDefs' ++ funsDefs)
distill' index t@(LTS (LTSTransitions term@(Free x) [(X' x', _)])) (CaseCtx context branches) funsNames previousGens funsDefs =
  if x == x'
    then
      let root = Case term branches
          firstBranch = (Case', t)
          distilledBranches = map ( \(branchName, args, resultTerm) -> let
                                                        resultTerm'' = substituteTermWithNewTerms resultTerm [(x', Con branchName $ map Free args)]
                                                      in distill index (place resultTerm'' context, EmptyCtx) funsNames previousGens funsDefs
                                            ) branches
          funsDefs' = nub $ concatMap fst distilledBranches
          distilledTerms = map snd distilledBranches
          otherBranches = zipWith (\(branchName, args, _) distilledTerm -> (CaseBranch' branchName args, distilledTerm)) branches distilledTerms
       in (nub $ funsDefs' ++ funsDefs, doLTSManyTr root $ firstBranch : otherBranches)
    else error "Error: got branch x -> (x,0), but label is not the same as x"
distill' index t@(LTS lts) (CaseCtx context branches) funsNames previousGens funsDefs =
  let root = Case (getOldTerm lts) branches
      firstBranch = (Case', t)
      distilledBranches = map (\(_, _, resultTerm) ->
                                       distill index (place resultTerm context, EmptyCtx) funsNames previousGens funsDefs) branches
      funsDefs' = nub $ concatMap fst distilledBranches
      distilledTerms = map snd distilledBranches
      otherBranches = zipWith (\(branchName, args, _) distilledTerm ->
        (CaseBranch' branchName args, distilledTerm)) branches distilledTerms
   in (nub $ funsDefs' ++ funsDefs, doLTSManyTr root $ firstBranch : otherBranches)
distill' _ _ _ _ _ _ = error "Got error during execution distill'."