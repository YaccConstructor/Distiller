module Residualizer (residualize) where
  
import TermType
import LTSType
import HelperTypes
import Debug.Trace (traceShow)
  
residualize :: LTS -> Term
residualize lts = residualize' lts []

-- lts --> [((funname, vars),expr)] -> prog
residualize' :: LTS -> [((String, [String]), Term)] -> Term
residualize' (LTS (LTSTransitions _ [(X' x, Leaf)])) _ = Free x
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
  in foldl (\accum (X' x_i, t_i) -> Let x_i (residualize' t_i eps) accum) initializer $ tail branches'
residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) eps | traceShow ("eps = " ++ show eps ++ show (filter (\((_, _), fundef) -> not $ null $ renaming fundef e) eps)) False = undefined  
residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) eps =
  case filter (\((_, _), fundef) -> not $ null $ renaming fundef e) eps of
    ((funname, vars), fundef) : _ -> let
        renamings = concat $ renaming fundef e
        result = foldl Apply (Fun funname) $ map snd renamings
        in result
    _ -> let
            xs = case t of
                Leaf -> error ("Error occured during residualization: unfolding of function " ++ funName ++ " is Leaf.")
                LTS transitions -> free $ getOldTerm transitions
            f = renameVar (map (fst . fst) eps) "f"
            result = residualize' t $ ((f, xs), e) : eps
        in foldl (flip Lambda) result xs
residualize' (LTS (LTSTransitions _ [(UnfoldBeta', t)])) eps = residualize' t eps
residualize' (LTS (LTSTransitions _ [(UnfoldCons' _, t)])) eps = residualize' t eps   
residualize' lts eps = error $ "LTS " ++ show lts ++ " with fun calls " ++ show eps ++ " not matched in residualization."      

  
  
