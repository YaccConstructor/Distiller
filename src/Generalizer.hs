module Generalizer where

import HelperTypes
import LTSType
import TermType

generalize :: LTS -> LTS -> [Generalization] -> LTS
generalize t t' prevGensAccum =
  let (tg, prevGensAccum') = generalize' t t' prevGensAccum [] []
   in _A tg prevGensAccum'

generalize' :: LTS -> LTS -> [Generalization] -> [String] -> [LTS] -> (LTS, [Generalization])
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
generalize' (LTS (LTSTransitions e ("case", t0) : branches))
            (LTS (LTSTransitions e ("case", t0') : branches')) 

branchesForConstructor :: [(String, LTS)] -> [(String, LTS)] -> Bool
branchesForConstructor branches branches' = all (\t -> tail (map fst t) == take (length t) createLabels) [branches, branches']

branchesForFunctionCall :: [(String, LTS)] -> [(String, LTS)] -> Bool
branchesForFunctionCall branches branches' = all (\t -> map fst t == ["@", "#1"]) [branches, branches']

branchesForLambda :: [(String, LTS)] -> [(String, LTS)] -> Bool
branchesForLambda [('\\' : _, _)] [('\\' : x', lts')] = True
branchesForLambda _ _ = False

_A :: LTS -> [Generalization] -> LTS
_A lts [] = lts

_B :: LTS -> [Generalization] -> LTS
_B lts [] = lts

_C :: LTS -> [Generalization] -> LTS
_C lts [] = lts
