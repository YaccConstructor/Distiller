module Generalizer where

import HelperTypes
import LTSType
import TermType
import Data.List
import HomeomorphicEmbeddingChecker
import Data.Bifunctor
import Debug.Trace (traceShow)
import Data.Map (Map)
import qualified Data.Map as Map

generalize :: LTS -> LTS -> [Generalization] -> LTS
generalize t t' prevGensAccum =
  let (tg, prevGensAccum') = generalize' t t' prevGensAccum [] []
   in _A tg prevGensAccum'

generalize' :: LTS -> LTS -> [Generalization] -> [String] -> [(String, String)] -> (LTS, [Generalization])
generalize' t@(LTS (LTSTransitions (Free x) _)) (LTS (LTSTransitions (Free x') _)) _ _ _ | traceShow ("t=" ++ x ++ ", t'=" ++ x') False = undefined
generalize' t@(LTS (LTSTransitions (Free _) _)) (LTS (LTSTransitions (Free _) _)) _ _ _ = (t, [])
generalize' (LTS (LTSTransitions e bs@(first@(Con' _, Leaf) : branches)))
            (LTS (LTSTransitions e' bs'@((Con' _, Leaf) : branches'))) _ _ _ | traceShow ("Matched with constructor: " ++ show e ++ show e' ++ show branches ++ show branches') False = undefined
generalize' (LTS (LTSTransitions e bs@(first@(Con' conname, Leaf) : branches)))
            (LTS (LTSTransitions _ bs'@((Con' conname', Leaf) : branches')))
            previousGensAccum boundVariables previousFunsAccum
  | branchesSetsForConstructor bs bs' = let
    terms = map snd branches
    terms' = map snd branches'
    tgs = zipWith3 (\t_i t_i' number -> (ConArg' number, generalize' t_i t_i' previousGensAccum boundVariables previousFunsAccum)) terms terms' createLabels
    tgs' = orderGeneralizations tgs
    newPreviousGensAccum = concatMap (snd . snd) tgs'
    newLtss = map (\(label, (lts, _)) -> (label, lts)) tgs'
    newLts = doLTSManyTr e $ first : newLtss
    in (newLts, newPreviousGensAccum)
  | otherwise = error "Constructor case, but branches have incorrect form."
generalize' (LTS (LTSTransitions e [(label@(Lambda' x), t)])) (LTS (LTSTransitions _ [(Lambda' _, t')])) _ _ _ | traceShow ("in lambda " ++ show e) False = undefined
generalize' (LTS (LTSTransitions e [(label@(Lambda' x), t)]))
            (LTS (LTSTransitions _ [(Lambda' _, t')]))
            previousGensAccum boundVariables previousFunsAccum = let
            tgs = generalize' t t' previousGensAccum (x : boundVariables) previousFunsAccum
            in (doLTS1Tr e label $ fst tgs, snd tgs)
generalize' (LTS (LTSTransitions e [(label@(Lambda' x), t)])) (LTS (LTSTransitions _ [(Lambda' _, t')])) _ _ _ | traceShow ("Apply0 " ++ show e) False = undefined
generalize' (LTS (LTSTransitions e [(Apply0', t0), (Apply1', t1)]))
            (LTS (LTSTransitions _ [(Apply0', t0'), (Apply1', t1')]))
            previousGensAccum boundVariables previousFunsAccum = let
    pair0 = generalize' t0 t0' previousGensAccum boundVariables previousFunsAccum
    pair1 = generalize' t1 t1' previousGensAccum boundVariables previousFunsAccum
    lst = [(Apply0', pair0), (Apply1', pair1)]
    lst' = orderGeneralizations lst
    newLtss = map (\(label, (tg, gen)) -> (label, tg)) lst'
    newPreviousGensAccum = concatMap (snd . snd) lst'
    newLts = doLTSManyTr e newLtss
    in (newLts, newPreviousGensAccum)
generalize' (LTS (LTSTransitions e ((Case', t0) : branches)))
            (LTS (LTSTransitions _ ((Case', t0') : branches')))
            previousGensAccum boundVariables previousFunsAccum
            | traceShow ("t_i t_i'" ++ show (zipWith (\(CaseBranch' p_i args, t_i) (CaseBranch' p_i' args', t_i') ->
                                 (t_i, t_i')
                                 ) branches branches')) False = undefined
generalize' (LTS (LTSTransitions e ((Case', t0) : branches)))
            (LTS (LTSTransitions _ ((Case', t0') : branches')))
            previousGensAccum boundVariables previousFunsAccum = let
    pair0 = generalize' t0 t0' previousGensAccum boundVariables previousFunsAccum
    tgs = zipWith (\(CaseBranch' p_i args, t_i) (CaseBranch' p_i' args', t_i') ->
        (CaseBranch' p_i args, generalize' t_i t_i' previousGensAccum (args ++ boundVariables) previousFunsAccum)
        ) branches branches'
    tgs' = orderGeneralizations $ (Case', pair0) : tgs
    newPreviousGensAccum = concatMap (snd . snd) tgs'
    newLtss = map (\(label, (lts, _)) -> (label, lts)) tgs'
    newLts = doLTSManyTr e newLtss
    in (newLts, newPreviousGensAccum)
generalize' (LTS (LTSTransitions e ((Let', t0) : branches))) (LTS (LTSTransitions _ ((Let', t0') : branches'))) _ _ _ | traceShow ("Let " ++ show e) False = undefined
generalize' (LTS (LTSTransitions e ((Let', t0) : branches)))
            (LTS (LTSTransitions _ ((Let', t0') : branches')))
            previousGensAccum boundVariables previousFunsAccum = let
    pair = generalize' t0 t0' previousGensAccum boundVariables previousFunsAccum
    tgs = zipWith (\(x_i, t_i) (_, t_i') ->
            (x_i, generalize' t_i t_i' previousGensAccum boundVariables previousFunsAccum)) branches branches'
    tgs' = orderGeneralizations $ (Let', pair) : tgs
    newPreviousGensAccum = concatMap (snd . snd) tgs'
    newLtss = map (\(x_i, (tg_i, _)) -> (x_i, tg_i)) tgs'
    newLts = doLTSManyTr e newLtss
    in (newLts, newPreviousGensAccum)
generalize' lts@(LTS (LTSTransitions e [(u@(Unfold' funName), t)]))
            (LTS (LTSTransitions _ [(Unfold' funName', t')]))
            previousGensAccum boundVariables previousFunsAccum =
    if (funName, funName') `elem` previousFunsAccum
        then (lts, [])
        else let
        (tg, newPreviousGensAccum) = generalize' t t' previousGensAccum boundVariables $ (:) (funName, funName') previousFunsAccum
        in (doLTS1Tr e u tg, newPreviousGensAccum)
generalize' (LTS (LTSTransitions e [(UnfoldBeta', t)]))
            (LTS (LTSTransitions _ [(UnfoldBeta', t')]))
            previousGensAccum boundVariables previousFunsAccum = generalize' t t' previousGensAccum boundVariables previousFunsAccum
generalize' (LTS (LTSTransitions e [(UnfoldCons' _, t)]))
            (LTS (LTSTransitions _ [(UnfoldCons' _, t')]))
            previousGensAccum boundVariables previousFunsAccum = generalize' t t' previousGensAccum boundVariables previousFunsAccum
generalize' t _ previousGensAccum boundVariables _ | traceShow ("Nothing mapped in t = " ++ show t ++ show previousGensAccum) False = undefined
generalize' t _ previousGensAccum boundVariables _ = let
    boundVariables' = intersect (getFreeVariables t) boundVariables
    t2 = _C t boundVariables'
    in case filter (\(x, t1) -> (not . null) $ isRenaming t1 t2) previousGensAccum of
        (x', _) : _ -> (_B (doLTS1Tr x' (X' $ show x') doLTS0Tr) boundVariables', [])
        [] -> let
            x = renameVar boundVariables' "x"
            fresh = Free x
            in (_B (doLTS1Tr fresh (X' x) doLTS0Tr) boundVariables', [(fresh, t2)])

orderGeneralizations :: [(Label, (LTS, [Generalization]))] -> [(Label, (LTS, [Generalization]))]
orderGeneralizations xs = let
    allGens = concatMap (\(label, (t_i, gens_i)) -> map (\(Free x, lts) -> (lts, x)) gens_i) xs
    accum = addCollectionToMap allGens Map.empty
    result = map (\(label, (t_i, gens)) -> let
        substitutions = map (\(Free x, lts) -> let
            x'' = case Map.lookup lts accum of
                Just x' -> x'
                Nothing -> error "Smething went wrong during ordering generalizations"
            in (x, x'', lts)) gens
        gens' = map (\(x, x'', lts) -> (Free x'', lts)) substitutions
        substitutions' = map (\(x, x'', lts) -> (x, x'')) substitutions    
        t_i' = renameVarInLtsRecursively substitutions' t_i
        in (label, (t_i', gens'))) xs
    in result

renameVarInLtsRecursively :: [(String, String)] -> LTS -> LTS
renameVarInLtsRecursively substitutions lts
  = foldl renameVarInLts lts substitutions

addCollectionToMap :: Ord k => [(k, a)] -> Map k a -> Map k a
addCollectionToMap ((a,b) : xs) myMap = addCollectionToMap xs $ Map.insert a b myMap
addCollectionToMap [] myMap = myMap

getFreeVariables :: LTS -> [String]
getFreeVariables Leaf = []
getFreeVariables (LTS lts@(LTSTransitions _ branches)) = free (getOldTerm lts) ++ concatMap (getFreeVariables . snd) branches

branchesForFunctionCall :: [(Label, LTS)] -> [(Label, LTS)] -> Bool
branchesForFunctionCall branches branches' = all (\t -> map fst t == [Apply0', Apply1']) [branches, branches']

branchesForLambda :: [(String, LTS)] -> [(String, LTS)] -> Bool
branchesForLambda [('\\' : _, _)] [('\\' : _, _)] = True
branchesForLambda _ _ = False

_A :: LTS -> [Generalization] -> LTS
_A t@(LTS (LTSTransitions root lts)) generalizations | traceShow ("in let root =" ++ show root) False = undefined
_A t@(LTS (LTSTransitions root _)) generalizations = let
    branches = map (\b -> case fst b of
      (Free x) -> (X' x, snd b)
      _ -> error "Generalization must have only free vars in the first element of pair") generalizations 
    in doLTSManyTr root $ (:) (Let', t) branches
_A _ _ = error "Unexpected lts or generalizations list got for _A function."

_B :: LTS -> [String] -> LTS
_B lts@(LTS (LTSTransitions t _)) bv | traceShow ("In _B with t =" ++ show t ++ " with bound vars " ++ concat bv) False = undefined
_B lts@(LTS (LTSTransitions t _)) (x1 : xs) = let
    initializer = doLTSManyTr t [(Apply0', lts), (Apply1', doLTS1Tr (Free x1) (X' x1) doLTS0Tr)] 
    in foldl (\lts' x_i -> doLTSManyTr t [(Apply0', lts'), (Apply1', doLTS1Tr (Free x_i) (X' x_i) doLTS0Tr)]) initializer xs
_B lts@(LTS (LTSTransitions t _)) [] = lts

_C :: LTS -> [String] -> LTS
_C lts@(LTS (LTSTransitions t _)) bv | traceShow ("In _C with t =" ++ show t ++ " with bound vars " ++ concat bv) False = undefined
_C lts@(LTS (LTSTransitions t _)) xs@(_ : _) = let
    xs' = reverse xs
    x_n = head xs'
    initializer = doLTS1Tr t (Lambda' x_n) lts 
    in foldl (\lts' x_i -> doLTS1Tr t (Lambda' x_i) lts') initializer xs
_C lts [] = lts
_C _ _ = error "Unexpected lts or bound variables list got for _C function."