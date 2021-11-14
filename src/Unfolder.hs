module Unfolder (unfold) where

import HelperTypes  
import TermType
    
unfold :: Term -> [FunctionDefinition] -> Term  
unfold term funsDefs = unfold' (term, EmptyCtx) [] funsDefs

unfold' :: TermInContext -> [(String, Term)] -> [FunctionDefinition] -> Term
unfold' (term@(Free x), context) letVarsAccum funsDefs = 
   case lookup x letVarsAccum of
       Just e -> unfold' (e, context) letVarsAccum funsDefs 
       Nothing -> place term context
unfold' (con@(Con _ _), context) _ _ = place con context
unfold' (lambda@(Lambda _ _ ), context) _ _ = place lambda context
unfold' (Fun funname, context) _ funsDefs = 
  case lookup funname funsDefs of
        Just (_, e) -> place e context 
        Nothing -> error $ "Function definition for " ++ funname ++ "not found during unfolding."
unfold' (Apply e0 e1, context) letVarsAccum funsDefs = unfold' (e0, ApplyCtx context e1) letVarsAccum funsDefs
unfold' (Case e0 branches, context) letVarsAccum funsDefs = unfold' (e0, CaseCtx context branches) letVarsAccum funsDefs
unfold' (Let x e0 e1, context) letVarsAccum funsDefs = Let x e0 $ unfold' (e1, context) ((x, e0) : letVarsAccum) funsDefs
unfold' (MultipleApply e0 e0funsDefs, context) letVarsAccum funsDefs = let
   e0' = unfold' (e0, context) letVarsAccum (e0funsDefs ++ funsDefs)  
   in MultipleApply e0' e0funsDefs



