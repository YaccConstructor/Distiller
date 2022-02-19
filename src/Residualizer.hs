module Residualizer (residualize) where
  
import TermType
import LTSType
import HelperTypes
import Debug.Trace (traceShow)
import Data.List (sort, (\\), nub)
  
residualize :: LTS -> [FunctionDefinition] -> (Term, [FunctionDefinition])
residualize lts funsDefs = let 
    funsDefs'' = map (\(funname, (args, term)) -> ((funname, args), term)) funsDefs
    (term', funsDefs') = residualize' lts [] funsDefs''
    convertedFunsDefs = nub $ map (\((funname, args), term) -> (funname, (args, term))) funsDefs'
    in (term', convertedFunsDefs)
    
-- lts --> [((funname, vars),expr)] -> prog
residualize' :: LTS -> [((String, [String]), Term)] -> [((String, [String]), Term)] -> (Term, [((String, [String]), Term)])
--residualize' lts eps funsDefs | traceShow ("in residualizer " ++ show lts ++ ", eps = " ++ show eps ++ show funsDefs) False = undefined
residualize' (LTS (LTSTransitions _ [(X' x, Leaf)])) eps funsDefs = (Free x, eps)
residualize' (LTS (LTSTransitions _ bs@((Con' conName, Leaf) : branches))) eps funsDefs
    | branchesSetForConstructor bs = let
        result = map ((\branch -> residualize' branch eps funsDefs) . snd) branches
        terms = map fst result
        funsDefs' = funsDefs ++ concatMap snd result
        in (Con conName terms, funsDefs')
    | otherwise = error $ "Trying to residualize: " ++ conName ++ " constructor case, but branches have incorrect form."
residualize' (LTS (LTSTransitions _ [(Lambda' x, t)])) eps funsDefs = let
    result = residualize' t eps funsDefs
    term = fst result
    funsDefs' = snd result
    in (Lambda x term, funsDefs ++ funsDefs')
residualize' (LTS (LTSTransitions _ [(Apply0', t0), (Apply1', t1)])) eps funsDefs = let
    result1 = residualize' t0 eps funsDefs
    result2 = residualize' t1 eps funsDefs
    in (Apply (fst result1) (fst result2), snd result1 ++ snd result2 ++ funsDefs)
residualize' (LTS (LTSTransitions _ ((Case', t0) : branches))) eps funsDefs = let
    caseResult = residualize' t0 eps funsDefs
    branchesResult = map (\(CaseBranch' p1 args, branch) -> (CaseBranch' p1 args, residualize' branch eps (funsDefs ++ snd caseResult))) branches
    branchesTerms = map (\(CaseBranch' p1 args, residualized) -> (p1, args, fst residualized)) branchesResult
    branchesFunsDefs = concatMap (\(CaseBranch' p1 args, residualized) -> snd residualized) branchesResult
    in (Case (fst caseResult) branchesTerms, funsDefs ++ (snd caseResult) ++ branchesFunsDefs)
residualize' (LTS (LTSTransitions _ ((Let', t0) : branches))) eps funsDefs = let
  t0' = residualize' t0 eps funsDefs
  
  branches' = reverse branches
  (X' x_n, t_n) = head branches'
  t_n' = residualize' t_n eps funsDefs
  
  initializer = (Let x_n (fst t_n') (fst t0'), snd t0')
  in foldl (\accum (X' x_i, t_i) -> let
    t_i' = residualize' t_i eps funsDefs
    in (Let x_i (fst t_i') (fst accum), snd accum ++ snd t_i')) initializer $ tail branches'
--residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) eps funsDefs | traceShow ("e = " ++ show e ++ ";funname = " ++ show funName ++ "; t = " ++ show t) False = undefined
residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) eps funsDefs = case t of
        Leaf ->  case lookup funName (map fst (funsDefs ++ eps)) of
                    Nothing -> error ("Error occured during residualization: unfolding of function " ++ funName ++ " is Leaf, but function have not occured before.")
                    Just _ -> do {
                      (e, funsDefs)
                      }
        LTS transitions -> case filter (\((_, _), fundef) -> not $ null $ concat $ termRenaming fundef $ getOldTerm transitions) funsDefs of
          ((funname, vars), fundef) : _ -> let
            residualized = residualize' t eps funsDefs
            renamings = concat $ termRenaming fundef $ getOldTerm transitions
            vars' = map (\var -> case lookup var renamings of
                                    Nothing -> var
                                    Just (Free var') -> var') vars
            in do {
            traceShow ("renaming passed!" ++ show t ++ ";;" ++ show e ++ ";" ++ show vars)
            (foldl (flip Lambda) (fst residualized) (reverse vars'), snd residualized ++ funsDefs)
            }
          _ -> let
                t' = getOldTerm transitions
                xs = free t'
                f = renameVar (map (fst . fst) eps) "f"
                result = residualize' t (((f, xs), e) : eps) (((f, xs), e) : funsDefs)
            in do {
              traceShow ("Renaming not passed " ++ show ((foldl (flip Lambda) (fst result) $ checkDefinitionHasLambdas t' xs, snd result ++ eps)))
              (foldl (flip Lambda) (fst result) $ checkDefinitionHasLambdas t' xs, snd result ++ funsDefs)
            }
residualize' (LTS (LTSTransitions _ [(UnfoldBeta', t)])) eps funsDefs = residualize' t eps funsDefs
residualize' (LTS (LTSTransitions _ [(UnfoldCons' _, t)])) eps funsDefs = residualize' t eps funsDefs
residualize' lts eps funsDefs = error $ "LTS " ++ show lts ++ " with fun calls " ++ show eps ++ " not matched in residualization."


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
  
