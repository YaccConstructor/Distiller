module Residualizer (residualize) where
  
import TermType
import LTSType
import HelperTypes  
  
residualize :: LTS -> Term
residualize lts = residualize' lts []

residualize' :: LTS -> [Term] -> Term
residualize' (LTS (LTSTransitions x'@(Free _) _)) _ = x'
residualize' (LTS (LTSTransitions _ bs@((Con' conName, Leaf) : branches))) eps
    | branchesSetForConstructor bs = Con conName $ map ((`residualize'` eps) . snd) branches
    | otherwise = error $ "Trying to residualize: " ++ conName ++ " constructor case, but branches have incorrect form."
residualize' (LTS (LTSTransitions _ [(Lambda' x, t)])) eps = Lambda x $ residualize' t eps
residualize' (LTS (LTSTransitions _ [(Apply0', t0), (Apply1', t1)])) eps = 
  Apply (residualize' t0 eps) (residualize' t1 eps)
residualize' (LTS (LTSTransitions _ ((Case', t0) : branches))) eps = 
  Case (residualize' t0 eps) $ map (\(CaseBranch' p1 args, branch) -> (p1, args, residualize' branch eps)) branches
residualize' (LTS (LTSTransitions _ ((Let', t0) : branches))) eps = let  
  t0' = residualize' t0 eps
  branches' = reverse branches
  (X' x_n, t_n) = head branches'
  initializer = Let x_n (residualize' t_n eps) t0' 
  in foldl (\accum (X' x_i, t_i) -> Let x_i (residualize' t_i eps) accum) initializer branches'
--fix implementation for f   
residualize' lts@(LTS (LTSTransitions e [(u@(Unfold' funName), t)])) eps = e  
residualize' (LTS (LTSTransitions _ [(UnfoldBeta', t)])) eps = residualize' t eps
residualize' (LTS (LTSTransitions _ [(UnfoldCons' _, t)])) eps = residualize' t eps   
residualize' lts eps = error $ "LTS " ++ show lts ++ " with fun calls " ++ show eps ++ " not matched in residualization."      

  
  
