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
--isRenaming' funNamesAccum t u freeVars boundVars renaming | traceShow ("isRenaming':" ++ show t ++ show u ++ show freeVars ++ show boundVars ++ show renaming) False = undefined
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

isHomeomorphicEmbedding lts1 lts2 = isHomeomorphicEmbedding' lts1 lts2

isHomeomorphicEmbedding' :: LTS -> LTS -> [(String, String)]
--isHomeomorphicEmbedding' t u | traceShow ("isHEmbedding: t = " ++ show t ++ " and u = " ++ show u) False = undefined
isHomeomorphicEmbedding' lts1 lts2 = concat $ coupled [] lts1 lts2 [] [] []

embed ::  [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [[(String, String)]]
--embed funNamesAccum lts1 lts2 freeVars boundVars renaming | traceShow ("embed: t = " ++ show lts1 ++ " and u = "
  --  ++ show lts2 ++ ", dived = " ++ show (dived funNamesAccum lts1 lts2 freeVars boundVars renaming)
   -- ++ show (coupled funNamesAccum lts1 lts2 freeVars boundVars renaming)) False = undefined
embed funNamesAccum lts1 lts2 freeVars boundVars renaming =
  sort $ nub (coupled funNamesAccum lts1 lts2 freeVars boundVars renaming ++ dived funNamesAccum lts1 lts2 freeVars boundVars renaming)

dived ::  [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [[(String, String)]]
--dived _ t u _ _ _ | traceShow ("dived : t = " ++ show t ++ " and u = " ++ show u) False = undefined
--dived funNamesAccum (LTS (LTSTransitions (Free x) _)) (LTS (LTSTransitions _ (_ : _))) _ _ _ = []
dived funNamesAccum lts1
                    lts2@(LTS (LTSTransitions _ branches'@([(Unfold' _, t)]))) freeVars boundVars renaming =
                      embed funNamesAccum lts1 t freeVars boundVars renaming
dived funNamesAccum lts1
                    lts2@(LTS (LTSTransitions _ branches'@([(Lambda' x, t)]))) freeVars boundVars renaming =
    -- if some i has embedding, than dived is passed
     embed funNamesAccum lts1 t freeVars boundVars renaming
dived funNamesAccum lts1
                    lts2@(LTS (LTSTransitions _ branches'@((Con' _, _) : _))) freeVars boundVars renaming =
    -- if some i has embedding, than dived is passed
    concat [embed funNamesAccum lts1 t' freeVars boundVars renaming | t' <- map snd branches']
{---dived funNamesAccum lts1@(LTS (LTSTransitions _ branches@((Apply0', LTS (LTSTransitions (Apply (Fun f) _) _)) : _)))
                    lts2@(LTS (LTSTransitions _ branches'@((Apply0', LTS (LTSTransitions (Apply (Fun g) _) _)) : _))) freeVars boundVars renaming
                    | f /= g = [] --}
dived funNamesAccum lts1
                    lts2@(LTS (LTSTransitions _ branches'@([(Apply0', t), (Apply1', u)]))) freeVars boundVars renaming =
    -- if some i has embedding, than dived is passed
    embed funNamesAccum lts1 t freeVars boundVars renaming ++ embed funNamesAccum lts1 u freeVars boundVars renaming
dived funNamesAccum lts1
                    lts2@(LTS (LTSTransitions _ ((Case', t) : branches))) freeVars boundVars renaming =
    -- if some i has embedding, than dived is passed
    embed funNamesAccum lts1 t freeVars boundVars renaming ++ concatMap (\(CaseBranch' c xs, t') -> embed funNamesAccum lts1 t' freeVars boundVars renaming) branches
dived funNamesAccum lts1
                    lts2@(LTS (LTSTransitions _ branches'@([(Let', t), (LetX' x, u)]))) freeVars boundVars renaming =
    -- if some i has embedding, than dived is passed
   embed funNamesAccum lts1 t freeVars boundVars renaming ++ embed funNamesAccum lts1 u freeVars boundVars renaming
--dived _ t u _ _ _ | traceShow ("in dived nothing matched : t = " ++ show t ++ " and u = " ++ show u) False = undefined
dived _ Leaf Leaf _ _ renaming = [renaming]
dived _ _ _ _ _ _ = []


-- if all i has embedding, than coupled is passed
coupled :: [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [[(String, String)]]
{---coupled _ t u _ _ r
     | traceShow ("coupled : t = " ++ show t ++ " and u = " ++ show u ++ show r) False = undefined
coupled _ t@(LTS (LTSTransitions (Free x) _)) u@(LTS (LTSTransitions (Free x') _)) _ _ renaming
    | traceShow ("coupled! : t = " ++ show t ++ " and u = " ++ show u ++ ", r = " ++ show renaming ++ show (if x `elem` map fst renaming
                                                                                                                                        then [renaming | (x,x') `elem` renaming]--}                                                                                                                                        
coupled funNamedAccum (LTS (LTSTransitions t@(Free x) _))
                      (LTS (LTSTransitions t'@(Free x') _)) freeVars boundVars renaming =
                        if x `elem` map fst renaming
                            then [renaming | (x,x') `elem` renaming]
                            else [(x,x'):renaming]
-- unfold
coupled funNamesAccum (LTS (LTSTransitions (Fun f) _))
                      (LTS (LTSTransitions (Fun g) _)) _ _ renaming | f /= g = []
coupled funNamesAccum (LTS (LTSTransitions _ [(Unfold' funName, t)]))
                      (LTS (LTSTransitions _ [(Unfold' funName', t')])) freeVars boundVars renaming
         | (funName, funName') `elem` funNamesAccum = [renaming]
         | otherwise = embed ((funName, funName') : funNamesAccum) t t' freeVars boundVars renaming
-- lambda
coupled funNamesAccum (LTS (LTSTransitions _ [(Lambda' x, t)]))
                          (LTS (LTSTransitions _ [(Lambda' x', t')])) freeVars boundVars renaming = embed funNamesAccum t t' freeVars boundVars renaming
{--coupled funNamesAccum (LTS (LTSTransitions _ [(Con' conName, Leaf)]))
                          (LTS (LTSTransitions _ [(Con' conName', Leaf)])) freeVars boundVars renaming | conName == conName' = [[("#","#")]]-}
-- constructor
coupled funNamesAccum (LTS (LTSTransitions _ bs@((Con' conName, Leaf) : branches)))
                          (LTS (LTSTransitions _ bs'@((Con' conName', Leaf) : branches'))) freeVars boundVars renaming
    | branchesSetsForConstructor bs bs' =
      if conName == conName' then let
        termPairs = zip (map snd branches) (map snd branches')
        in foldr (\(t,t') rs -> concat [embed funNamesAccum t t' freeVars boundVars renaming' | renaming' <- rs]) [renaming] termPairs
      else []
-- Apply
coupled funNamesAccum (LTS (LTSTransitions (Apply (Fun f) _) [(Apply0', _), (Apply1', u)]))
                        (LTS (LTSTransitions (Apply (Fun g) _) [(Apply0', _), (Apply1', u')])) _ _ _ | traceShow ("f = " ++ show f ++ ", g = " ++ show g) False = undefined
coupled funNamesAccum (LTS (LTSTransitions (Apply (Fun f) _) [(Apply0', _), (Apply1', u)]))
                                              (LTS (LTSTransitions (Apply (Fun g) _) [(Apply0', _), (Apply1', u')])) _ _ _ | f /= g = []
coupled funNamesAccum  (LTS (LTSTransitions _ [(Apply0', t), (Apply1', u)]))
                           (LTS (LTSTransitions _ [(Apply0', t'), (Apply1', u')])) freeVars boundVars renaming =
   concat [embed funNamesAccum u u' freeVars boundVars renaming' | renaming' <- coupled funNamesAccum t t' freeVars boundVars renaming]
-- let
coupled funNamesAccum (LTS (LTSTransitions _ [(Let', t), (LetX' x, u)]))
                          (LTS (LTSTransitions _ [(Let', t'), (LetX' x', u')])) freeVars boundVars renaming =
                            concat [embed funNamesAccum u u' freeVars boundVars renaming' | renaming' <- embed funNamesAccum t t' freeVars boundVars renaming]
-- case
coupled funNamesAccum (LTS (LTSTransitions _ ((Case', t) : branches)))
                                  (LTS (LTSTransitions _ ((Case', t') : branches'))) freeVars boundVars renaming
                                  | traceShow ("coupled case, t = " ++ show t ++ ", t' = " ++ show t' ++ show (embed funNamesAccum t t' freeVars boundVars renaming)) False = undefined
coupled funNamesAccum (LTS (LTSTransitions _ ((Case', t) : branches)))
                          (LTS (LTSTransitions _ ((Case', t') : branches'))) freeVars boundVars renaming
    | matchCase branches branches' = let
        --initializer = embed funNamesAccum t t' freeVars boundVars renaming
        branchess = zip branches branches'
        in foldr (\((CaseBranch' c xs, u),(CaseBranch' c' xs', u')) rs
            -> concat [embed funNamesAccum u u' freeVars boundVars renaming' | renaming' <- rs]) (embed funNamesAccum t t' freeVars boundVars renaming) branchess
coupled _ Leaf Leaf _ _ renaming = [renaming]
--coupled _ t u _ _ _ | traceShow ("IN coupling nothing matched for t = " ++ show t ++ " and u = " ++ show u) False = undefined
coupled _ _ _ _ _ _ = []

