module HomeomorphicEmbeddingChecker (isRenaming, isHomeomorphicEmbedding) where

import TermType
import LTSType
import HelperTypes
import Debug.Trace (traceShow)
import Data.List

isRenaming :: LTS -> LTS -> [(String, String)]
isRenaming Leaf (LTS _) = []
isRenaming (LTS _) Leaf = []
isRenaming Leaf Leaf = []
isRenaming lts1@(LTS (LTSTransitions e1 _)) lts2@(LTS (LTSTransitions e2 _))= sort $ nub $ isRenaming' [] lts1 lts2 (free e1 ++ free e2) [] []

isRenaming' :: [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [(String, String)]
isRenaming' funNamesAccum t u freeVars boundVars renaming | traceShow ("isRenaming':" ++ show t ++ show u ++ show freeVars ++ show boundVars ++ show renaming) False = undefined
isRenaming' funNamesAccum (LTS (LTSTransitions t@(Free x) _))
                                     (LTS (LTSTransitions t'@(Free x') _)) freeVars boundVars renaming
               | x == x' = renaming                      
               | x `elem` boundVars && t' == t = renaming
               | x `elem` boundVars && t' /= t = []
               | x `elem` freeVars = if (x,x') `elem` renaming
                       then renaming
                       else (x,x') : renaming
-- unfold
isRenaming' funNamesAccum (LTS (LTSTransitions _ [(Unfold' funName, t)]))
                          (LTS (LTSTransitions _ [(Unfold' funName', t')])) freeVars boundVars renaming =
    if (funName, funName') `elem` funNamesAccum
        then renaming
        else isRenaming' ((funName, funName') : funNamesAccum) t t' freeVars boundVars renaming
-- lambda
isRenaming' funNamesAccum (LTS (LTSTransitions _ [(Lambda' x, t)]))
                          (LTS (LTSTransitions _ [(Lambda' x', t')])) freeVars boundVars renaming = let
        x'' = renameVar freeVars x
        in isRenaming' funNamesAccum t t' (x'' : freeVars) boundVars renaming
-- constructor
isRenaming' funNamesAccum (LTS (LTSTransitions _ bs@((Con' conName, Leaf) : branches)))
                          (LTS (LTSTransitions _ bs'@((Con' conName', Leaf) : branches'))) freeVars boundVars renaming
    | branchesSetsForConstructor bs bs' =
      if conName == conName' then let
        termPairs = zip (map snd branches) (map snd branches')
        in foldr (\(t, t') renaming' -> renaming' ++ isRenaming' funNamesAccum t t' freeVars boundVars renaming') renaming termPairs
        else error "During renaming check got branches not matched for constructor."
-- Apply
isRenaming' funNamesAccum  (LTS (LTSTransitions _ [(Apply0', t), (Apply1', u)]))
                           (LTS (LTSTransitions _ [(Apply0', t'), (Apply1', u')])) freeVars boundVars renaming = let
    a = isRenaming' funNamesAccum t t' freeVars boundVars renaming
    b = isRenaming' funNamesAccum u u' freeVars boundVars a in b
-- let
isRenaming' funNamesAccum (LTS (LTSTransitions _ [(Let', t), (LetX' x, u)]))
                          (LTS (LTSTransitions _ [(Let', t'), (LetX' x', u')])) freeVars boundVars renaming = let
    x'' = renameVar freeVars x
    a = isRenaming' funNamesAccum t t' freeVars boundVars renaming
    b = isRenaming' funNamesAccum u u' (x'' : freeVars) (x'' : boundVars) a in b
-- case
isRenaming' funNamesAccum (LTS (LTSTransitions _ ((Case', t) : branches)))
                          (LTS (LTSTransitions _ ((Case', t') : branches'))) freeVars boundVars renaming
    | matchCase branches branches' = let
        initializer = isRenaming' funNamesAccum t t' freeVars boundVars renaming 
        branchess = zip branches branches'
        in foldr (\((CaseBranch' name xs, u), (CaseBranch' name' xs', u')) renaming' -> let 
            freeVars' = renameVars freeVars xs
            xs'' = take (length xs) freeVars'
            in isRenaming' funNamesAccum u u' freeVars' (xs'' ++ boundVars) renaming') initializer branchess
isRenaming' _ t u _ _ renaming = []
   
isHomeomorphicEmbedding :: LTS -> LTS -> [(String, String)]
isHomeomorphicEmbedding t u | traceShow ("isHEmbedding: t = " ++ show t ++ " and u = " ++ show u) False = undefined
isHomeomorphicEmbedding lts1 lts2 = coupled [] lts1 lts2 [] [] []

embed ::  [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [(String, String)]
embed _ t u _ _ _ | traceShow ("embed: t = " ++ show t ++ " and u = " ++ show u) False = undefined
embed funNamesAccum lts1 lts2 freeVars boundVars renaming =
  sort $ nub $ dived funNamesAccum lts1 lts2 freeVars boundVars renaming ++ coupled funNamesAccum lts1 lts2 freeVars boundVars renaming

dived ::  [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [(String, String)]
dived _ t u _ _ _ | traceShow ("dived : t = " ++ show t ++ " and u = " ++ show u) False = undefined
dived funNamesAccum lts1 lts2@(LTS (LTSTransitions _ branches')) freeVars boundVars renaming =
    -- if some i has embedding, than dived is passed
    concatMap (\t -> embed funNamesAccum lts1 t freeVars boundVars renaming) (map snd branches')
dived _ _ _ _ _ _ = []


-- if all i has embedding, than coupled is passed
coupled :: [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [(String, String)]
coupled _ t@(LTS (LTSTransitions (Free x) _)) u@(LTS (LTSTransitions (Free x') _)) _ _ _
    | traceShow ("coupled : t = " ++ show t ++ " and u = " ++ show u) False = undefined
coupled funNamedAccum (LTS (LTSTransitions t@(Free x) _))
                      (LTS (LTSTransitions t'@(Free x') _)) freeVars boundVars renaming =
                        if  (x,x') `elem` renaming
                            then renaming
                            else (x,x') : renaming
-- unfold
coupled funNamesAccum (LTS (LTSTransitions _ [(Unfold' funName, t)]))
                      (LTS (LTSTransitions _ [(Unfold' funName', t')])) freeVars boundVars renaming
         | (funName, funName') `elem` funNamesAccum = renaming
         | otherwise = embed ((funName, funName') : funNamesAccum) t t' freeVars boundVars renaming
-- lambda
coupled funNamesAccum (LTS (LTSTransitions _ [(Lambda' x, t)]))
                          (LTS (LTSTransitions _ [(Lambda' x', t')])) freeVars boundVars renaming = let
        x'' = renameVar freeVars x
        in embed funNamesAccum t t' (x'' : freeVars) boundVars renaming
-- constructor
coupled _ t@(LTS (LTSTransitions _ bs@((Con' conName, Leaf) : branches))) u@(LTS (LTSTransitions _ bs'@((Con' conName', Leaf) : branches'))) _ _ _
    | traceShow ("coupled cons : t = " ++ show t ++ " and u = " ++ show u) False = undefined
coupled funNamesAccum (LTS (LTSTransitions _ bs@((Con' conName, Leaf) : branches)))
                          (LTS (LTSTransitions _ bs'@((Con' conName', Leaf) : branches'))) freeVars boundVars renaming
    | branchesSetsForConstructor bs bs' =
      if conName == conName' then let
        termPairs = zip (map snd branches) (map snd branches')
        in foldr (\(t, t') renaming' -> renaming' ++ embed funNamesAccum t t' freeVars boundVars renaming') renaming termPairs
        else []
-- Apply
coupled funNamesAccum  (LTS (LTSTransitions _ [(Apply0', t), (Apply1', u)]))
                           (LTS (LTSTransitions _ [(Apply0', t'), (Apply1', u')])) freeVars boundVars renaming = let
    a = embed funNamesAccum t t' freeVars boundVars renaming
    b = embed funNamesAccum u u' freeVars boundVars a in b
-- let
coupled funNamesAccum (LTS (LTSTransitions _ [(Let', t), (LetX' x, u)]))
                          (LTS (LTSTransitions _ [(Let', t'), (LetX' x', u')])) freeVars boundVars renaming = let
    x'' = renameVar freeVars x
    a = embed funNamesAccum t t' freeVars boundVars renaming
    b = embed funNamesAccum u u' (x'' : freeVars) (x'' : boundVars) a in b
-- case
coupled funNamesAccum (LTS (LTSTransitions _ ((Case', t) : branches)))
                                  (LTS (LTSTransitions _ ((Case', t') : branches'))) freeVars boundVars renaming
                                  | traceShow ("coupled (case,t) (case, t)" ++ show (embed funNamesAccum t t' freeVars boundVars renaming)) False = undefined
coupled funNamesAccum (LTS (LTSTransitions _ ((Case', t) : branches)))
                          (LTS (LTSTransitions _ ((Case', t') : branches'))) freeVars boundVars renaming
    | matchCase branches branches' = let
        initializer = embed funNamesAccum t t' freeVars boundVars renaming
        branchess = zip branches branches'
        in foldr (\((CaseBranch' name xs, u), (CaseBranch' name' xs', u')) renaming' -> let
                    freeVars' = renameVars freeVars xs
                    xs'' = take (length xs) freeVars'
                    in embed funNamesAccum u u' freeVars' (xs'' ++ boundVars) renaming') initializer branchess
coupled _ t u _ _ _ | traceShow ("Nothing matched for t = " ++ show t ++ " and u = " ++ show u) False = undefined
coupled _ _ _ _ _ _ = []

