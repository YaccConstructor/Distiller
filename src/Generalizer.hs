module Generalizer where

-- generalisation of terms

generaliseTerm t u = generalise t u (free t++free u) [] []

generalise t u fv s1 s2 | isEmbedding t u = generalise' t u fv s1 s2
generalise t u fv s1 s2 = case find (\(x,t') -> t==t' && (lookup x s2 == Just u)) s1 of
                                               Just (x,t') -> (Free x,s1,s2)
                                               Nothing -> let x = renameVar (fv++map fst s1) "x"
                                                          in  (Free x,(x,t):s1,(x,u):s2)

generalise' (Free x) (Free x') fv s1 s2 = (Free x,s1,s2)
generalise' (Bound i) (Bound i') fv s1 s2 = (Bound i,s1,s2)
generalise' (Lambda x t) (Lambda x' t') fv s1 s2 = let x'' = renameVar (fv++map fst s1) x
                                                       (t'',s1',s2') = generalise (concrete x'' t) (concrete x'' t') (x'':fv) s1 s2
                                                   in  (Lambda x (abstract t'' x''),s1',s2')
generalise' (Con c ts) (Con c' ts') fv s1 s2 = let ((s1',s2'),ts'') = mapAccumL (\(s1,s2) (t,t') -> let (t'',s1',s2') = generalise t t' fv s1 s2
                                                                                                    in  ((s1',s2'),t'')) (s1,s2) (zip ts ts')
                                               in  (Con c ts'',s1',s2')
generalise' (Apply t u) (Apply t' u') fv s1 s2 = let (t'',s1',s2') = generalise t t' fv s1 s2
                                                     (u'',s1'',s2'') = generalise u u' fv s1' s2'         
                                                 in  (Apply t'' u'',s1'',s2'')
generalise' (Fun f) (Fun f') fv s1 s2 = (Fun f,s1,s2)
generalise' (Case t bs) (Case t' bs') fv s1 s2 = let (t'',s1',s2') = generalise t t' fv s1 s2
                                                     ((s1'',s2''),bs'') = mapAccumL (\(s1,s2) ((c,xs,t),(c',xs',t')) -> let fv' = renameVars (fv++map fst s1) xs
                                                                                                                            xs'' = take (length xs) fv'
                                                                                                                            (t'',s1',s2') = generalise (foldr concrete t xs'') (foldr concrete t' xs'') fv' s1 s2
                                                                                                                        in ((s1',s2'),(c,xs,foldl abstract t'' xs''))) (s1',s2') (zip bs bs')
                                                 in  (Case t'' bs'',s1'',s2'')
generalise' (Let x t u) (Let x' t' u') fv s1 s2 = let x'' = renameVar (fv++map fst s1) x
                                                      (t'',s1',s2') = generalise t t' fv s1 s2
                                                      (u'',s1'',s2'') = generalise (concrete x'' u) (concrete x'' u') (x'':fv) s1' s2'
                                                  in  (Let x t'' (abstract u'' x''),s1'',s2'')

-- function renaming

funRenaming t u = renamingFun [] t u (free t ++ free u) []

renamingFun ls (Free x) (Free x') fv r = if x `elem` map fst r
                                         then [r | (x,x') `elem` r]
                                         else [(x,x'):r]
renamingFun ls (Bound i) (Bound i') fv r | i==i' = [r]
renamingFun ls (Lambda x t) (Lambda x' t') fv r = let x'' = renameVar fv x
                                                  in  renamingFun ls (concrete x'' t) (concrete x'' t') (x'':fv) r
renamingFun ls (Con c ts) (Con c' ts') fv r | c==c' = foldr (\(t,t') rs -> concat [renamingFun ls t t' fv r | r <- rs]) [r] (zip ts ts')
renamingFun ls (Apply t u) (Apply t' u') fv r = concat [renamingFun ls u u' fv r' | r' <- renamingFun ls t t' fv r]
renamingFun ls (Fun f) (Fun f') fv r | f==f' = [r]
renamingFun ls (Case t bs) (Case t' bs') fv r | matchCase bs bs' = foldr (\((c,xs,t),(c',xs',t')) rs -> let fv' = renameVars fv xs
                                                                                                            xs'' = take (length xs) fv'
                                                                                                        in  concat [renamingFun ls (foldr concrete t xs'') (foldr concrete t' xs'') fv' r | r <- rs]) (renamingFun ls t t' fv r) (zip bs bs')
renamingFun ls (Let x t u) (Let x' t' u') fv r = let x'' = renameVar fv x
                                                 in  concat [renamingFun ls (concrete x'' u) (concrete x'' u') (x'':fv) r' | r' <- renamingFun ls t t' fv r]
renamingFun ls (Unfold l t u) (Unfold l' t' u' ) fv r = renamingFun ((l,l'):ls) u u' fv r
renamingFun ls (Fold l t) (Fold l' t') fv r = if   l `elem` map fst ls
                                              then [r | (l,l') `elem` ls]
                                              else renamingFun ls t t' fv r 
renamingFun ls t t' fv r = []

-- embedding of functions

funEmbedding t u = coupleFun [] t u (free t ++ free u) []

embedFun ls t u fv r = coupleFun ls t u fv r ++ diveFun ls t u fv r

coupleFun ls (Free x) (Free x') fv r = if   x `elem` map fst r
                                       then [r | (x,x') `elem` r]
                                       else [(x,x'):r]
coupleFun ls (Bound i) (Bound i') fv r | i == i' = [r]
coupleFun ls (Lambda x t) (Lambda x' t') fv r = let x'' = renameVar fv x
                                                in  embedFun ls (concrete x'' t) (concrete x'' t')  (x'':fv) r
coupleFun ls (Con c ts) (Con c' ts') fv r | c==c' = foldr (\(t,t') rs -> concat [embedFun ls t t' fv r | r <- rs]) [r] (zip ts ts')
coupleFun ls (Apply t u) (Apply t' u') fv r = concat [embedFun ls u u' fv r' | r' <- coupleFun ls t t' fv r]
coupleFun ls (Fun f) (Fun f') fv r | f==f' = [r]
coupleFun ls (Case t bs) (Case t' bs') fv r | matchCase bs bs' = foldr (\((c,xs,t),(c',xs',t')) rs -> let fv' = renameVars fv xs
                                                                                                          xs'' = take (length xs) fv'
                                                                                                      in  concat [embedFun ls (foldr concrete t xs'') (foldr concrete t' xs'') fv' r | r <- rs]) (embedFun ls t t' fv r) (zip bs bs')
coupleFun ls (Let x t u) (Let x' t' u') fv r  = let x'' = renameVar fv x
                                                in  concat [embedFun ls (concrete x'' u) (concrete x'' u') (x'':fv) r' | r' <- embedFun ls t t' fv r]
coupleFun ls (Unfold l t u) (Unfold l' t' u' ) fv r = embedFun ((l,l'):ls) u u' fv r
coupleFun ls (Fold l t) (Fold l' t') fv r = if   l `elem` map fst ls
                                            then [r | (l,l') `elem` ls]
                                            else coupleFun ls t t' fv r 
coupleFun ls t t' fv r = []

diveFun ls t (Lambda x t') fv r = let x' = renameVar fv x
                                  in  embedFun ls t (concrete x' t') (x':fv) r
diveFun ls t (Con c ts) fv r = concat [embedFun ls t t' fv r | t' <- ts]
diveFun ls t (Apply t' u) fv r = embedFun ls t t' fv r ++ embedFun ls t u fv r
diveFun ls t (Case t' bs) fv r = embedFun ls t t' fv r ++ concatMap (\(c,xs,t') -> let fv' = renameVars fv xs
                                                                                       xs' = take (length xs) fv'
                                                                                   in  embedFun ls t (foldr concrete t' xs') fv' r) bs
diveFun ls t (Let x t' u) fv r = let x' = renameVar fv x
                                 in  embedFun ls t t' fv r ++ embedFun ls t (concrete x' u) (x':fv) r
diveFun ls t (Unfold l t' u) fv r = embedFun ls t u fv r
diveFun ls t t' fv r = []

-- generalisation of functions

funGeneralise t u = generaliseFun [] t u (free t ++ free u) [] [] []

generaliseFun ls t u fv bv s1 s2 | not (null (coupleFun ls t u (fv++bv) [])) = generaliseFun' ls t u fv bv s1 s2
generaliseFun ls (Apply t (Free x)) u fv bv s1 s2 = let (t',s1',s2') = generaliseFun ls t (Lambda x (abstract u x)) fv bv s1 s2
                                                    in  (Apply t' (Free x),s1',s2')
generaliseFun ls (Free x) t fv bv s1 s2 | x `elem` fv = (Free x,s1,(x,t):s2)
generaliseFun ls t u fv bv s1 s2 = let xs = free t
                                       t' = foldl (\t x -> Lambda x (abstract t x)) t xs
                                       u' = foldl (\t x -> Lambda x (abstract t x)) u xs
                                       x = renameVar (fv++bv++map fst s1) "x"
                                   in  (foldr (\x t -> Apply t (Free x)) (Free x) xs,(x,t'):s1,(x,u'):s2)

generaliseFun' ls (Free x) (Free x') fv bv s1 s2 = (Free x,s1,s2)
generaliseFun' ls (Bound i) (Bound i') fv bv s1 s2 = (Bound i,s1,s2)
generaliseFun' ls (Lambda x t) (Lambda x' t') fv bv s1 s2 = let x'' = renameVar (fv++bv++map fst s1) "x"
                                                                (t'',s1',s2') = generaliseFun ls (concrete x'' t) (concrete x'' t') fv (x'':bv) s1 s2
                                                            in  (Lambda x (abstract t'' x''),s1',s2')
generaliseFun' ls (Con c ts) (Con c' ts') fv bv s1 s2 = let ((s1',s2'),ts'') = mapAccumL (\(s1,s2) (t,t') -> let (t'',s1',s2') = generaliseFun ls t t' fv bv s1 s2
                                                                                                             in  ((s1',s2'),t'')) (s1,s2) (zip ts ts')
                                                        in  (Con c ts'',s1',s2')
generaliseFun' ls (Apply t u) (Apply t' u') fv bv s1 s2 = let (t'',s1',s2') = generaliseFun ls t t' fv bv s1 s2
                                                              (u'',s1'',s2'') = generaliseFun ls u u' fv bv s1' s2'         
                                                          in  (Apply t'' u'',s1'',s2'')
generaliseFun' ls (Fun f) (Fun f') fv bv s1 s2 = (Fun f,s1,s2)
generaliseFun' ls (Case t bs) (Case t' bs') fv bv s1 s2 = let (t'',s1',s2') = generaliseFun ls t t' fv bv s1 s2
                                                              ((s1'',s2''),bs'') = mapAccumL (\(s1,s2) ((c,xs,t),(c',xs',t')) -> let vs = renameVars (fv++bv++map fst s1) xs
                                                                                                                                     xs'' = take (length xs) vs
                                                                                                                                     (t'',s1',s2') = generaliseFun ls (foldr concrete t xs'') (foldr concrete t' xs'') fv (xs''++bv) s1 s2
                                                                                                                                 in ((s1',s2'),(c,xs,foldl abstract t'' xs''))) (s1',s2') (zip bs bs')
                                                          in  (Case t'' bs'',s1'',s2'')
generaliseFun' ls (Let x t u) (Let x' t' u') fv bv s1 s2 = let x'' = renameVar (fv++bv++map fst s1) x
                                                               (t'',s1',s2') = generaliseFun ls t t' fv bv s1 s2
                                                               (u'',s1'',s2'') = generaliseFun ls (concrete x'' u) (concrete x'' u') fv (x'':bv) s1' s2'
                                                           in  (Let x t'' (abstract u'' x''),s1'',s2'')
generaliseFun' ls (Unfold l t u) (Unfold l' t' u') fv bv s1 s2 = let (u'',s1',s2') = generaliseFun ((l,l'):ls) u u' fv bv s1 s2
                                                                 in  (Unfold l t u'',s1',s2')
generaliseFun' ls (Fold l t) (Fold l' t') fv bv s1 s2 = (Fold l t,s1,s2)



makeLet s t = foldl (\u (x,t) -> Let x t (abstract u x)) t s

makeLet' s t = foldl (\u (x,t) -> case t of
                                     Free _ -> subst t (abstract u x)
                                     _ -> Let x t (abstract u x)) t s
                                     
                                     
-- free variables in a term

free t = nub (free' t)

free' (Free x) = [x]
free' (Bound i) = []
free' (Lambda x t) = free' t
free' (Con c ts) = concatMap free' ts
free' (Apply t u)  = free' t ++ free' u
free' (Fun f) = []
free' (Case t bs) = free' t ++ concatMap (\(c,xs,t) -> free' t) bs
free' (Let x t u) = free' t  ++ free' u
free' (Unfold l t u) = free' u
free' (Fold l t) = free' t

-- folds in a term

folds (Free x) = []
folds (Bound i) = []
folds (Lambda x t) = folds t
folds (Con c ts) = concatMap folds ts
folds (Apply t u)  = folds t ++ folds u
folds (Fun f) = []
folds (Case t bs) = folds t ++ concatMap (\(c,xs,t) -> folds t) bs
folds (Let x t u) = folds t  ++ folds u
folds (Unfold l t u) = filter (/=l) (folds u)
folds (Fold l t) = [l]

-- funs in a prog

funs (t,d) = funs' d t []

funs' d (Free x) fs = fs
funs' d (Bound i) fs = fs
funs' d (Lambda x t) fs = funs' d t fs
funs' d (Con c ts) fs = foldr (funs' d) fs ts
funs' d (Apply t u) fs = funs' d t (funs' d u fs)
funs' d (Fun f) fs = if   f `elem` fs
                     then fs
                     else case lookup f d of
                             Nothing -> f:fs
                             Just (xs,t)  -> funs' d t (f:fs)
funs' d (Case t bs) fs = foldr (\(_,_,t) fs -> funs' d t fs) (funs' d t fs) bs
funs' d (Let x t u) fs = funs' d t (funs' d u fs)

-- shift global de Bruijn indices by i, where current depth is d

shift = shift' 0

shift' d 0 u = u
shift' d i (Free x) = Free x
shift' d i (Bound i') = if i' >= d then Bound (i'+i) else Bound i'
shift' d i (Lambda x t) = Lambda x (shift' (d+1) i t)
shift' d i (Con c ts) = Con c (map (shift' d i) ts)
shift' d i (Apply t u) = Apply (shift' d i t) (shift' d i u)
shift' d i (Fun f) = Fun f
shift' d i (Case t bs) = Case (shift' d i t) (map (\(c,xs,t) -> (c,xs,shift' (d+length xs) i t)) bs)
shift' d i (Let x t u) = Let x (shift' d i t) (shift' (d+1) i u)
shift' d i (Unfold l t u) = Unfold l (shift' d i t) (shift' (d+1) i u)
shift' d i (Fold l t) = Fold l (shift' d i t) 

-- substitute term t for variable with de Bruijn index i

subst = subst' 0

subst' i t (Free x) = Free x
subst' i t (Bound i')
   | i'<i      = Bound i'
   | i'==i     = shift i t
   | otherwise = Bound (i'-1)
subst' i t (Lambda x t') = Lambda x (subst' (i+1) t t')
subst' i t (Con c ts) = Con c (map (subst' i t) ts)
subst' i t (Apply t' u) = Apply (subst' i t t') (subst' i t u)
subst' i t (Fun f) = Fun f
subst' i t (Case t' bs) = Case (subst' i t t') (map (\(c,xs,u) -> (c,xs,subst' (i+length xs) t u)) bs)
subst' i t (Let x t' u) = Let x (subst' i t t') (subst' (i+1) t u)
subst' i t (Unfold l t' u) = Unfold l (subst' i t t') (subst' (i+1) t u)
subst' i t (Fold l t') = Fold l (subst' i t t')

-- rename a term t using renaming r

rename r (Free x) = case lookup x r of
                       Just x'  -> Free x'
                       Nothing -> Free x
rename r (Bound i) = Bound i
rename r (Lambda x t) = Lambda x (rename r t)
rename r (Con c ts) = Con c (map (rename r) ts)
rename r (Apply t u) = Apply (rename r t) (rename r u)
rename r (Fun f) = Fun f
rename r (Case t bs) = Case (rename r t) (map (\(c,xs,t) -> (c,xs,rename r t)) bs)
rename r (Let x t u) = Let x (rename r t) (rename r u)
rename r (Unfold l t u) = Unfold l (rename r t) (rename r u)
rename r (Fold l t) = Fold l (rename r t) 

-- instantiate a term t using substitution s

instantiate = instantiate' 0

instantiate' d s (Free x) = case lookup x s of
                               Just t  -> shift d t
                               Nothing -> Free x
instantiate' d s (Bound i) = Bound i
instantiate' d s (Lambda x t) = Lambda x (instantiate' (d+1) s t)
instantiate' d s (Con c ts) = Con c (map (instantiate' d s) ts)
instantiate' d s (Apply t u) = Apply (instantiate' d s t) (instantiate' d s u)
instantiate' d s (Fun f) = Fun f
instantiate' d s (Case t bs) = Case (instantiate' d s t) (map (\(c,xs,t) -> (c,xs,instantiate' (d+length xs) s t)) bs)
instantiate' d s (Let x t u) = Let x (instantiate' d s t) (instantiate' (d+1) s u)
instantiate' d s (Unfold l t u) = Unfold l (instantiate' d s t) (instantiate' (d+1) s u)
instantiate' d s (Fold l t) = Fold l (instantiate' d s t) 

-- replace variable x with de Bruijn index

abstract = abstract' 0

abstract' i (Free x') x = if x==x' then Bound i else Free x'
abstract' i (Bound i') x = if i'>=i then Bound (i'+1) else Bound i'
abstract' i (Lambda x' t) x = Lambda x' (abstract' (i+1) t x)
abstract' i (Con c ts) x = Con c (map (\t -> abstract' i t x) ts)
abstract' i (Apply t u) x = Apply (abstract' i t x) (abstract' i u x)
abstract' i (Fun f) x = Fun f
abstract' i (Case t bs) x = Case (abstract' i t x) (map (\(c,xs,t) -> (c,xs,abstract' (i+length xs) t x)) bs)
abstract' i (Let x' t u) x = Let x' (abstract' i t x) (abstract' (i+1) u x)
abstract' i (Unfold l t u) x = Unfold l (abstract' i t x) (abstract' (i+1) u x)
abstract' i (Fold l t) x = Fold l (abstract' i t x) 

-- replace de Bruijn index 0 with variable x

concrete = concrete' 0

concrete' i x (Free x') = Free x'
concrete' i x (Bound i')
   | i'<i = Bound i'
   | i'==i = Free x
   | otherwise = Bound (i'-1)
concrete' i x (Lambda x' t) = Lambda x' (concrete' (i+1) x t)
concrete' i x (Con c ts) = Con c (map (concrete' i x) ts)
concrete' i x (Apply t u) = Apply (concrete' i x t) (concrete' i x u)
concrete' i x (Fun f) = Fun f
concrete' i x (Case t bs) = Case (concrete' i x t) (map (\(c,xs,t) -> (c,xs,concrete' (i+length xs) x t)) bs)
concrete' i x (Let x' t u) = Let x' (concrete' i x t) (concrete' (i+1) x u)
concrete' i x (Unfold l t u) = Unfold l (concrete' i x t) (concrete' (i+1) x u)
concrete' i x (Fold l t) = Fold l (concrete' i x t) 

-- rename variable x so it does not clash with any of fv

renameVar fv x = if   x `elem` fv
                 then renameVar fv (x++"'")
                 else x

renameVars = foldr (\x fv -> let x' = renameVar fv x in x':fv)

-- unfold function

unfold (Apply t u,d) = let t' = unfold (t,d)
                       in  Apply t' u
unfold (Case t bs,d) = let t' = unfold (t,d)
                       in  Case t' bs
unfold (Fun f,d) = case lookup f d of
                    Nothing -> error ("Undefined function: "++f)
                    Just (xs,t) -> foldr Lambda t xs
unfold (t,d) = t                                     