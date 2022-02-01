module Unfolder (unfold) where

import HelperTypes  
import TermType
import Debug.Trace (traceShow, trace)

unfold :: Term -> [FunctionDefinition] -> Term  
unfold term funsDefs = unfold' (term, EmptyCtx) funsDefs [] 

unfold' :: TermInContext -> [FunctionDefinition] -> [(String, Term)] -> Term
unfold' x funDefs letVarsAccum | traceShow (show x ++ ";" ++ show funDefs ++ ";" ++ show letVarsAccum) False = undefined
unfold' (term@(Free x), context) funsDefs letVarsAccum = 
   case lookup x letVarsAccum of
       Just e -> unfold' (e, context) funsDefs letVarsAccum 
       Nothing -> place term context
unfold' (con@(Con _ _), context) _ _ = place con context
unfold' (lambda@(Lambda _ _ ), context) _ _ = place lambda context
--unfold' (Fun funname, context) funsDefs _ | traceShow ("funname:" ++ show funname ++ show (place e context)) False = undefined
unfold' (Fun funname, context) funsDefs _ = 
  case lookup funname funsDefs of
        Just (_, e) -> do {
          trace ("funname:" ++ show funname ++ show (place e context))
          place e context
          } 
        Nothing -> error $ "Function definition for " ++ funname ++ " not found in " ++ show funsDefs ++ " during unfolding." 
unfold' (Apply e0 e1, context) funsDefs letVarsAccum = unfold' (e0, ApplyCtx context e1) funsDefs letVarsAccum 
unfold' (Case e0 branches, context) funsDefs letVarsAccum = unfold' (e0, CaseCtx context branches) funsDefs letVarsAccum 
unfold' (Let x e0 e1, context) funsDefs letVarsAccum = Let x e0 $ unfold' (e1, context) funsDefs ((x, e0) : letVarsAccum)
unfold' (MultipleApply e0 e0funsDefs, context) funsDefs letVarsAccum = let
   e0' = unfold' (e0, context) (e0funsDefs ++ funsDefs) letVarsAccum   
   in MultipleApply e0' e0funsDefs



