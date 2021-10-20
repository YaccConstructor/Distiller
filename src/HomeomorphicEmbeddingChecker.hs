module HomeomorphicEmbeddingChecker where

-- homeomorphic embedding of terms

isEmbedding t u = not (null(embedding t u))

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
