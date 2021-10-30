module HomeomorphicEmbeddingChecker (isRenaming, isHomeomorphicEmbedding) where


import TermType
import LTSType
import HelperTypes

isRenaming :: LTS -> LTS -> [(String, Term)]
isRenaming lts1 lts2 = isRenaming' [] lts1 lts2 [] [] []

isRenaming' :: Foldable t => [(String, String)] -> LTS -> LTS -> [String] -> t String -> [(String, Term)] -> [(String, Term)]
isRenaming' funNamesAccum (LTS (LTSTransitions t@(Free x) _))
                          (LTS (LTSTransitions t'@(Free x') _)) freeVars boundVars renaming
    | x `elem` freeVars && t' == t = renaming
    | x `elem` freeVars = []
    | x `elem` boundVars = if x `elem` map fst renaming
        then if (x,t) `elem` renaming
            then renaming
            else (x,t) : renaming
        else []
isRenaming' funNamesAccum (LTS (LTSTransitions _ [('*' : funName, t)]))
                          (LTS (LTSTransitions _ [('*' : funName', t')])) freeVars boundVars renaming = 
    if (funName, funName') `elem` funNamesAccum
        then renaming
        else isRenaming' ((funName, funName') : funNamesAccum) t t' freeVars boundVars renaming
isRenaming' funNamesAccum (LTS (LTSTransitions _ [('\\' : x, t)]))
                          (LTS (LTSTransitions _ [('\\' : x', t')])) freeVars boundVars renaming = let 
        x'' = renameVar freeVars x
        in isRenaming' funNamesAccum t t' (x'' : freeVars) boundVars renaming     
isRenaming' funNamesAccum (LTS (LTSTransitions _ bs@((conName, Leaf) : branches)))
                          (LTS (LTSTransitions _ bs'@((conName', Leaf) : branches'))) freeVars boundVars renaming
    | branchesForConstructor bs bs' = 
      if conName == conName' then let
        termPairs = zip (map snd branches) (map snd branches')
        in foldr (\(t, t') renaming' -> renaming' ++ isRenaming' funNamesAccum t t' freeVars boundVars renaming') renaming termPairs
        else []                         
{--inst' fs (Lambda x t) (Lambda x' t') fv bv s = let x'' = renameVar fv x
                                               in  inst' fs (concrete x'' t) (concrete x'' t') (x'':fv) (x'':bv) s
inst' fs (Con c ts) (Con c' ts') fv bv s | c==c' = foldr (\(t,t') ss -> concat [inst' fs t t' fv bv s | s <- ss]) [s] (zip ts ts')
inst' fs (Apply t u) (Apply t' u') fv bv s = concat [inst' fs u u' fv bv s' | s' <- inst' fs t t' fv bv s]
inst' fs (Fun f) (Fun f') fv bv s | f==f' = [s]
inst' fs (Case t bs) (Case t' bs') fv bv s | matchCase bs bs' = foldr (\((c,xs,t),(c',xs',t')) ss -> let fv' = renameVars fv xs
                                                                                                         xs'' = take (length xs) fv'
                                                                                                     in  concat [inst' fs (foldr concrete t xs'') (foldr concrete t' xs'') fv' (xs''++bv) s | s <- ss]) (inst' fs t t' fv bv s) (zip bs bs')
inst' fs (Let x t u) (Let x' t' u') fv bv s = let x'' = renameVar fv x
                                              in  concat [inst' fs (concrete x'' u) (concrete x'' u') (x'':fv) (x'':bv) s' | s' <- inst' fs t t' fv bv s]-}    
    

isHomeomorphicEmbedding :: LTS -> LTS -> [(String, String)]
isHomeomorphicEmbedding lts1 lts2 = []

-- homeomorphic embedding of terms

{--isEmbedding t u = not (null(embedding t u))

embedding t u = couple t u []

embed t u r = couple t u r ++ dive t u r 

couple (Free x) (Free x') r = if x `elem` map fst r then [r | (x,x') `elem` r] else [(x,x'):r]
couple (Bound i) (Bound i') r | i == i' = [r]
couple (Lambda x t) (Lambda x' t') r = embed t t' r
couple (Con c ts) (Con c' ts') r | c==c' = foldr (\(t,t') rs -> concat [embed t t' r | r <- rs]) [r] (zip ts ts')
couple (Apply t u) (Apply t' u') r = concat [embed u u' r' | r' <- couple t t' r]
couple (Fun f) (Fun f') r | f==f' = [r]
couple (Case t bs) (Case t' bs') r | matchCase bs bs' = foldr (\((c,xs,t),(c',xs',t')) rs -> concat [embed t t' r | r <- rs]) (embed t t' r) (zip bs bs')
couple (Let x t u) (Let x' t' u') r = concat [embed u u' r' | r' <- embed t t' r]
couple t t' r = []

dive t (Lambda x t') r = embed t (concrete x t') r
dive t (Con c ts) r = concat [embed t t' r | t' <- ts]
dive t (Apply t' u) r = embed t t' r ++ embed t u r
dive t (Case t' bs) r = embed t t' r ++ concatMap (\(c,xs,t') -> embed t (foldr concrete t' xs) r) bs
dive t (Let x t' u) r = embed t t' r ++ embed t (concrete x u) r
dive t t' r = []
--}