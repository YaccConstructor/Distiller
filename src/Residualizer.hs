module Residualizer (residualize) where
  
import TermType
import LTSType
import HelperTypes
import Debug.Trace (traceShow)
  
residualize :: LTS -> [FunctionDefinition] -> (Term, [FunctionDefinition])
residualize lts funsDefs = let 
    funsDefs'' = map (\(funname, (args, term)) -> ((funname, args), term)) funsDefs
    (term', funsDefs') = residualize' lts funsDefs''
    convertedFunsDefs = map (\((funname, args), term) -> (funname, (args, term))) funsDefs' 
    in (term', convertedFunsDefs)
    
-- lts --> [((funname, vars),expr)] -> prog
residualize' :: LTS -> [((String, [String]), Term)] -> (Term, [((String, [String]), Term)])
residualize' lts _ | traceShow ("in residualizer " ++ show lts) False = undefined
residualize' (LTS (LTSTransitions _ [(X' x, Leaf)])) eps = (Free x, eps)
residualize' (LTS (LTSTransitions _ bs@((Con' conName, Leaf) : branches))) eps
    | branchesSetForConstructor bs = let
        result = map ((`residualize'` eps) . snd) branches
        terms = map fst result
        eps' = eps ++ concatMap snd result
        in (Con conName terms, eps')
    | otherwise = error $ "Trying to residualize: " ++ conName ++ " constructor case, but branches have incorrect form."
residualize' (LTS (LTSTransitions _ [(Lambda' x, t)])) eps = let
    result = residualize' t eps
    term = fst result
    eps' = snd result
    in (Lambda x term, eps' ++ eps)
residualize' (LTS (LTSTransitions _ [(Apply0', t0), (Apply1', t1)])) eps = let
    result1 = residualize' t0 eps
    result2 = residualize' t1 eps
    in (Apply (fst result1) (fst result2), snd result1 ++ snd result2 ++ eps)
residualize' (LTS (LTSTransitions _ ((Case', t0) : branches))) eps = let
    caseResult = (residualize' t0 eps)
    branchesResult = map (\(CaseBranch' p1 args, branch) -> (CaseBranch' p1 args, residualize' branch eps)) branches
    branchesTerms = map (\(CaseBranch' p1 args, residualized) -> (p1, args, fst residualized)) branchesResult
    branchesEps = concatMap (\(CaseBranch' p1 args, residualized) -> snd residualized) branchesResult
    in (Case (fst caseResult) branchesTerms, eps ++ (snd caseResult) ++ branchesEps)
residualize' (LTS (LTSTransitions _ ((Let', t0) : branches))) eps = let  
  t0' = residualize' t0 eps
  
  branches' = reverse branches
  (X' x_n, t_n) = head branches'
  t_n' = residualize' t_n eps
  
  initializer = (Let x_n (fst t_n') (fst t0'), snd t0')
  in foldl (\accum (X' x_i, t_i) -> let
    t_i' = residualize' t_i eps
    in (Let x_i (fst t_i') (fst accum), snd accum ++ snd t_i')) initializer $ tail branches'
residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) eps | traceShow ("eps = " ++ show eps ++ show (filter (\((_, _), fundef) -> not $ null $ termRenaming fundef e) eps)) False = undefined
residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) eps =
  case filter (\((_, _), fundef) -> not $ null $ termRenaming fundef e) eps of
    ((funname, vars), fundef) : _ -> let
        renamings = concat $ termRenaming fundef e
        result = foldl Apply (Fun funname) $ map snd renamings
        in (result, eps)
    _ -> case t of 
        Leaf ->  case lookup funName (map fst eps) of
                    Nothing -> error ("Error occured during residualization: unfolding of function " ++ funName ++ " is Leaf, but function have not occured before.")
                    Just _ -> (Fun funName, eps)
        LTS transitions -> let
                xs = free $ getOldTerm transitions
                f = renameVar (map (fst . fst) eps) "f"
                result = residualize' t $ ((f, xs), e) : eps
            in (foldl (flip Lambda) (fst result) xs, snd result ++ eps)
residualize' (LTS (LTSTransitions _ [(UnfoldBeta', t)])) eps = residualize' t eps
residualize' (LTS (LTSTransitions _ [(UnfoldCons' _, t)])) eps = residualize' t eps   
residualize' lts eps = error $ "LTS " ++ show lts ++ " with fun calls " ++ show eps ++ " not matched in residualization."      

  
  
