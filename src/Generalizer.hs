module Generalizer where

import HelperTypes
import LTSType
import TermType
import Data.List
import HomeomorphicEmbeddingChecker
import Data.Bifunctor

generalize :: LTS -> LTS -> [Generalization] -> LTS
generalize t t' prevGensAccum =
  let (tg, prevGensAccum') = generalize' t t' prevGensAccum [] []
   in _A tg prevGensAccum'

generalize' :: LTS -> LTS -> [Generalization] -> [String] -> [(String, String)] -> (LTS, [Generalization])
generalize' t@(LTS (LTSTransitions (Free _) _)) (LTS (LTSTransitions (Free _) _)) _ _ _ = (t, [])
generalize' (LTS (LTSTransitions e (first@(_, Leaf) : branches)))
            (LTS (LTSTransitions _ ((_, Leaf) : branches')))
            previousGensAccum boundVariables previousFunsAccum
  | branchesForConstructor branches branches' = let
    terms = map snd branches
    terms' = map snd branches'
    tgs = zipWith (\t_i t_i' -> generalize' t_i t_i' previousGensAccum boundVariables previousFunsAccum) terms terms'
    newLtss = zip createLabels $ map fst tgs
    newPreviousGensAccum = concatMap snd tgs
    newLts = doLTSManyTr e $ first : newLtss
    in (newLts, newPreviousGensAccum)
  | otherwise = error "Constructor case, but branches have incorrect form."
generalize' (LTS (LTSTransitions e [(label@('\\' : x), t)]))
            (LTS (LTSTransitions _ [('\\' : _, t')]))
            previousGensAccum boundVariables previousFunsAccum = let
            tgs = generalize' t t' previousGensAccum (x : boundVariables) previousFunsAccum
            in (doLTS1Tr e label $ fst tgs, snd tgs)
generalize' (LTS (LTSTransitions e [("@", t0), ("#1", t1)]))
            (LTS (LTSTransitions _ [("@", t0'), ("#1", t1')]))
            previousGensAccum boundVariables previousFunsAccum = let
    (tg_0, previousGensAccum_0) = generalize' t0 t0' previousGensAccum boundVariables previousFunsAccum
    (tg_1, previousGensAccum_1) = generalize' t1 t1' previousGensAccum boundVariables previousFunsAccum
    newLts = doLTSManyTr e [("@", tg_0), ("#1", tg_1)]
    in (newLts, previousGensAccum_0 ++ previousGensAccum_1)
generalize' (LTS (LTSTransitions' e (("case", [], t0) : branches)))
            (LTS (LTSTransitions' _ (("case", [], t0') : branches')))
            previousGensAccum boundVariables previousFunsAccum = let
    (tg_0, previousGensAccum_0) = generalize' t0 t0' previousGensAccum boundVariables previousFunsAccum
    tgs = zipWith (\(p_i, args, t_i) (_, _, t_i') ->
        (generalize' t_i t_i' previousGensAccum (args ++ boundVariables) previousFunsAccum, (p_i, args))) branches branches'
    newPreviousGensAccum = previousGensAccum_0 ++ concatMap (snd . fst) tgs
    newLtss = map (\((tg_i, _), (p_i, args)) -> (p_i, args, tg_i)) tgs
    newLts = doLTSManyTr' e $ ("case", [], tg_0) : newLtss
    in (newLts, newPreviousGensAccum)
generalize' (LTS (LTSTransitions e (("let", t0) : branches)))
            (LTS (LTSTransitions _ (("let", t0') : branches')))
            previousGensAccum boundVariables previousFunsAccum = let
    (tg_0, previousGensAccum_0) = generalize' t0 t0' previousGensAccum boundVariables previousFunsAccum
    tgs = zipWith (\(x_i, t_i) (_, t_i') ->
            (x_i, generalize' t_i t_i' previousGensAccum boundVariables previousFunsAccum)) branches branches'
    newPreviousGensAccum = previousGensAccum_0 ++ concatMap (snd . snd) tgs
    newLtss = map (\(x_i, (tg_i, _)) -> (x_i, tg_i)) tgs
    newLts = doLTSManyTr e $ ("let", tg_0) : newLtss
    in (newLts, newPreviousGensAccum)
generalize' lts@(LTS (LTSTransitions e [(funName, t)]))
            (LTS (LTSTransitions _ [(funName', t')]))
            previousGensAccum boundVariables previousFunsAccum =
    if (funName, funName') `elem` previousFunsAccum
        then (lts, [])
        else let
        (tg, newPreviousGensAccum) = generalize' t t' previousGensAccum boundVariables $ (:) (funName, funName') previousFunsAccum
        in (doLTS1Tr e funName tg, newPreviousGensAccum)
generalize' (LTS (LTSTransitions e [("unfoldBeta", t)]))
            (LTS (LTSTransitions _ [("unfoldBeta", t')]))
            previousGensAccum boundVariables previousFunsAccum = generalize' t t' previousGensAccum boundVariables previousFunsAccum
generalize' (LTS (LTSTransitions e [("unfoldCons", t)]))
            (LTS (LTSTransitions _ [("unfoldCons", t')]))
            previousGensAccum boundVariables previousFunsAccum = generalize' t t' previousGensAccum boundVariables previousFunsAccum
generalize' t _ previousGensAccum boundVariables _ = let
    boundVariables' = intersect (getFreeVariables t) boundVariables
    t2 = _C t boundVariables'
    in case filter (\(x, t1) -> (not . null) $ isRenaming t1 t2) previousGensAccum of
        (x', _) : _ -> (_B (doLTS1Tr x' (show x') doLTS0Tr) boundVariables', [])
        [] -> let
            fresh = Free "x"
            in (_B (doLTS1Tr fresh (show fresh) doLTS0Tr) boundVariables', [(fresh, t2)])

getFreeVariables :: LTS -> [String]
getFreeVariables Leaf = []
getFreeVariables (LTS lts@(LTSTransitions _ branches)) = free (getOldTerm lts) ++ concatMap (getFreeVariables . snd) branches
getFreeVariables (LTS lts@(LTSTransitions' _ branches)) = free (getOldTerm lts) ++ concatMap (\(_, _, lts') -> getFreeVariables lts') branches

branchesForConstructor :: [(String, LTS)] -> [(String, LTS)] -> Bool
branchesForConstructor branches branches' = all (\t -> tail (map fst t) == take (length t) createLabels) [branches, branches']

branchesForFunctionCall :: [(String, LTS)] -> [(String, LTS)] -> Bool
branchesForFunctionCall branches branches' = all (\t -> map fst t == ["@", "#1"]) [branches, branches']

branchesForLambda :: [(String, LTS)] -> [(String, LTS)] -> Bool
branchesForLambda [('\\' : _, _)] [('\\' : _, _)] = True
branchesForLambda _ _ = False

_A :: LTS -> [Generalization] -> LTS
_A t@(LTS (LTSTransitions root _)) generalizations = doLTSManyTr root $ (:) ("let", t) $ map (Data.Bifunctor.first show) generalizations
_A _ _ = error "Unexpected lts or generalizations list got for _A function."

_B :: LTS -> [String] -> LTS
_B lts@(LTS (LTSTransitions t _)) (x1 : xs) = let
    initializer = doLTSManyTr t [("@", lts), ("#1", doLTS1Tr (Free x1) x1 doLTS0Tr)] 
    in foldl (\lts' x_i -> doLTSManyTr t [("@", lts'), ("#1", doLTS1Tr (Free x_i) x_i doLTS0Tr)]) initializer xs
_B _ _ = error "Unexpected lts or bound variables list got for _B function."    

_C :: LTS -> [String] -> LTS
_C lts@(LTS (LTSTransitions t _)) xs = let 
    xs' = reverse xs
    x_n = head xs'
    initializer = doLTS1Tr t ("\\" ++ x_n) lts 
    in foldl (\lts' x_i -> doLTS1Tr t ("\\" ++ x_i) lts') initializer xs
_C _ _ = error "Unexpected lts or bound variables list got for _B function."    