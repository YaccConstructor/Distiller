module Residualizer (residualize) where
  
import TermType
import LTSType
import HelperTypes
import Debug.Trace (traceShow)
import Data.List (sort, (\\), nub)
  
residualize :: LTS -> [FunctionDefinition] -> (Term, [FunctionDefinition])
residualize lts funsDefs = let 
    funsDefs'' = map (\(funname, (args, term)) -> ((funname, args), term)) funsDefs
    (term', funsDefs') = residualize' lts funsDefs''
    convertedFunsDefs = nub $ map (\((funname, args), term) -> (funname, (args, term))) funsDefs'
    in (term', convertedFunsDefs)
    
-- lts --> [((funname, vars),expr)] -> prog
residualize' :: LTS -> [((String, [String]), Term)] -> (Term, [((String, [String]), Term)])
--residualize' lts eps | traceShow ("in residualizer " ++ show lts ++ ", eps = " ++ show eps) False = undefined
residualize' (LTS (LTSTransitions _ [(X' x, Leaf)])) eps = (Free x, eps)
residualize' (LTS (LTSTransitions _ bs@((Con' conName, Leaf) : branches))) eps
    | branchesSetForConstructor bs = let
        result = map ((\branch -> residualize' branch eps) . snd) branches
        terms = map fst result
        eps' = eps ++ concatMap snd result
        in (Con conName terms, eps')
    | otherwise = error $ "Trying to residualize: " ++ conName ++ " constructor case, but branches have incorrect form."
residualize' (LTS (LTSTransitions _ [(Lambda' x, t)])) eps = let
    result = residualize' t eps
    term = fst result
    eps' = snd result
    in (Lambda x term, eps ++ eps')
residualize' (LTS (LTSTransitions _ [(Apply0', t0), (Apply1', t1)])) eps = let
    result1 = residualize' t0 eps
    result2 = residualize' t1 eps
    in (Apply (fst result1) (fst result2), snd result1 ++ snd result2 ++ eps)
residualize' (LTS (LTSTransitions _ ((Case', t0) : branches))) eps = let
    caseResult = residualize' t0 eps
    branchesResult = map (\(CaseBranch' p1 args, branch) -> (CaseBranch' p1 args, residualize' branch (eps ++ snd caseResult))) branches
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
--residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) eps | traceShow ("e = " ++ show e ++ ";funname = "
  --  ++ show funName ++ "; t = " ++ show t ++ ";" ++ show eps ++ "; renaming = " ++ show (filter (\((_, _), fundef) -> not $ null $ concat $ termRenaming fundef e) eps)) False = undefined
residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) eps =
        case filter (\((_, _), fundef) -> not $ null $ concat $ termRenaming fundef e) eps of
          ((funname, vars), fundef) : _ -> let
            renamings = concat $ termRenaming fundef e
            vars' = map (\var -> case lookup var renamings of
                                    Nothing -> Free var
                                    Just var' -> var') vars
            in do {
            traceShow ("renaming passed!" ++ show t ++ ";;" ++ show e ++ ";" ++ show vars ++ "; result = " ++ show (foldl (Apply) (Fun funname) (vars')))
            (foldl (Apply) (Fun funname) (vars'), eps)
            }
          _ -> let
                t' = case t of
                  Leaf -> e
                  LTS transitions -> getOldTerm transitions
                xs = free t'
                f = renameVar (map (fst . fst) eps) "f"
                result = residualize' t (((f, xs), e) : eps)
                resultWithLambdas = foldl (flip Lambda) (fst result) $ checkDefinitionHasLambdas t' xs
                resultWithLambdasAndApplies = foldl (Apply) (resultWithLambdas) $ reverse $ map Free $ checkDefinitionHasLambdas t' xs
            in do {
              traceShow ("Renaming not passed " ++ show e ++ "; t = " ++ show t ++ "; eps = " ++ show eps ++ show ((f, xs), e))
              (resultWithLambdasAndApplies, ((f, xs), e) : snd result ++ eps)
            }
residualize' (LTS (LTSTransitions _ [(UnfoldBeta', t)])) eps = residualize' t eps
residualize' (LTS (LTSTransitions _ [(UnfoldCons' _, t)])) eps = residualize' t eps
residualize' lts eps = error $ "LTS " ++ show lts ++ " with fun calls " ++ show eps ++ " not matched in residualization."


-- to prevent residualizer from generating more and more lambdas during creating new function f
-- checks that function definition already has set of lambdas in the top of expression (already residualized)
checkDefinitionHasLambdas :: Term -> [String] -> [String]
checkDefinitionHasLambdas term xs = let 
    lambdasInTerm = getLambdasInDefinition term []
    in xs \\ lambdasInTerm

getLambdasInDefinition :: Term -> [String] -> [String]
getLambdasInDefinition (Lambda x t@(Lambda x' term)) xs = getLambdasInDefinition t (x : xs)
getLambdasInDefinition (Lambda x term) xs = x : xs
getLambdasInDefinition _ _ = []  
  
