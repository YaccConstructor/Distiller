module Residualizer (residualize, getFirst, getSecond, getThird) where
  
import TermType
import LTSType
import HelperTypes
import Debug.Trace (traceShow)
import Data.List (sort, (\\), nub)
  
residualize :: LTS -> [FunctionDefinition] -> (Term, [FunctionDefinition], [FunctionDefinition])
residualize = residualize'
    
-- lts --> [((funname, vars),expr)] -> prog
residualize' :: LTS -> [FunctionDefinition] -> (Term, [FunctionDefinition], [FunctionDefinition])
--residualize' lts funsDefs | traceShow ("in residualizer " ++ show lts ++ ", funsDefs = " ++ show funsDefs) False = undefined
residualize' (LTS (LTSTransitions _ [(X' x, Leaf)])) funsDefs = (Free x, funsDefs, [])
residualize' (LTS (LTSTransitions _ bs@((Con' conName, Leaf) : branches))) funsDefs
    | branchesSetForConstructor bs = let
        residualized = map ((`residualize'` funsDefs) . snd) branches
        terms = map getFirst residualized
        funsDefs' = nub $ funsDefs ++ concatMap getSecond residualized
        in (Con conName terms, funsDefs', nub $ concatMap getThird residualized)
    | otherwise = error $ "Trying to residualize: " ++ conName ++ " constructor case, but branches have incorrect form."
residualize' (LTS (LTSTransitions _ [(Lambda' x, t)])) funsDefs = let
    result = residualize' t funsDefs
    term = getFirst result
    funsDefs' = getSecond result
    in (Lambda x term, nub $ funsDefs ++ funsDefs', getThird result)
residualize' (LTS (LTSTransitions _ [(Apply0', t0), (Apply1', t1)])) funsDefs = let
    result1 = residualize' t0 funsDefs
    result2 = residualize' t1 funsDefs
    funsDefs' = nub $ getSecond result1 ++ getSecond result2 ++ funsDefs
    funNamesAccum = getThird result1 ++ getThird result2
    in (Apply (getFirst result1) (getFirst result2), funsDefs', funNamesAccum)
residualize' (LTS (LTSTransitions _ ((Case', t0) : branches))) funsDefs = let
    caseResult = residualize' t0 funsDefs
    branchesResult = map (\(CaseBranch' p1 args, branch) -> (CaseBranch' p1 args, residualize' branch (funsDefs ++ getSecond caseResult))) branches

    branchesTerms = map (\(CaseBranch' p1 args, residualized) -> (p1, args, getFirst residualized)) branchesResult

    branchesfunsDefs = nub $ concatMap (\(CaseBranch' p1 args, residualized) -> getSecond residualized) branchesResult
    funsDefs' = nub $ funsDefs ++ getSecond caseResult ++ branchesfunsDefs

    branchesFunNamesAccum = nub $ concatMap (\(CaseBranch' p1 args, residualized) -> getThird residualized) branchesResult
    funNamesAccum = nub $ getThird caseResult ++ branchesFunNamesAccum

    in (Case (getFirst caseResult) branchesTerms, funsDefs', funNamesAccum)
residualize' (LTS (LTSTransitions _ ((Let', t0) : branches))) funsDefs = let
  t0' = residualize' t0 funsDefs
  
  branches' = reverse branches
  (X' x_n, t_n) = head branches'
  t_n' = residualize' t_n funsDefs
  
  initializer = (Let x_n (getFirst t_n') (getFirst t0'), getSecond t0', getThird t0')
  in foldl (\accum (X' x_i, t_i) -> let
    t_i' = residualize' t_i funsDefs
    in (Let x_i (getFirst t_i') (getFirst accum), getSecond accum ++ getSecond t_i', nub $ getThird accum ++ getThird t_i')) initializer $ tail branches'
residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) funsDefs | traceShow ("e = " ++ show e ++ ";funname = "
   ++ show funName ++ "; t = " ++ show t ++ ";" ++ show (nub funsDefs) ++ "; renaming = " ++ show (filter (\(_, (_, fundef)) -> not $ null $ concat $ termRenaming fundef e) funsDefs)) False = undefined
residualize' (LTS (LTSTransitions e [(Unfold' funName, t)])) funsDefs =
        case filter (\(_, (_, fundef)) -> not $ null $ concat $ termRenaming fundef e) funsDefs of
          (funname, (vars, fundef)) : _ -> let
            renamings = concat $ termRenaming fundef e
            vars' = map (\var -> case lookup var renamings of
                                    Nothing -> Free var
                                    Just var' -> var') vars
            in do {
            traceShow ("renaming passed!" ++ show t ++ ";;" ++ show e ++ ";" ++ show vars ++ "; result = " ++ show (foldl (Apply) (Fun funname) (vars')))
            (foldl Apply (Fun funname) (vars'), funsDefs, [])
            }
          _ -> let
                        t' = case t of
                                                Leaf -> e
                                                LTS transitions -> getOldTerm transitions
                        xs = free t'
                        f = renameVar (map fst funsDefs) "f"
                        residualized = residualize' t ((f, (xs, e)) : funsDefs)
                        resultWithLambdas = foldl (flip Lambda) (getFirst residualized) $ checkDefinitionHasLambdas t' xs
                        resultWithLambdasAndApplies = foldl (Apply) (resultWithLambdas) $ reverse $ map Free $ checkDefinitionHasLambdas t' xs
                    in do {
                        traceShow ("Renaming not passed " ++ show e ++ "; t = " ++ show t ++ "; funsDefs = " ++ show funsDefs ++ show ((f, xs), e) ++ show (((f, xs), getFirst residualized)))
                        (resultWithLambdasAndApplies, nub $ (f, (xs, getFirst residualized)) : (f, (xs, e)) : getSecond residualized ++ funsDefs, nub $ (f, (xs, getFirst residualized)) : getThird residualized)
                    }
residualize' (LTS (LTSTransitions _ [(UnfoldBeta', t)])) funsDefs = residualize' t funsDefs
residualize' (LTS (LTSTransitions _ [(UnfoldCons' _, t)])) funsDefs = residualize' t funsDefs
residualize' lts funsDefs = error $ "LTS " ++ show lts ++ " with fun calls " ++ show funsDefs ++ " not matched in residualization."

getThird :: (Term, [FunctionDefinition], [FunctionDefinition]) -> [FunctionDefinition]
getThird (_, _, z) = z

getSecond :: (Term, [FunctionDefinition], [FunctionDefinition]) -> [FunctionDefinition]
getSecond (_, y, _) = y

getFirst :: (Term, [FunctionDefinition], [FunctionDefinition]) -> Term
getFirst (x, _, _) = x

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
  
