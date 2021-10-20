module Residualizer where

-- Program residualisation

residualise t = residualise' [] t (free t)

residualise' ls (Free x) fv d e = (Free x,d,e)
residualise' ls (Bound i) fv d e = (Bound i,d,e)
residualise' ls (Lambda x t) fv d e = let x' = renameVar fv x
                                          (t',d',e') = residualise' ls (concrete x' t) (x':fv) d e
                                      in  (Lambda x (abstract t' x'),d',e')
residualise' ls (Con c ts) fv d e = let ((d',e'),ts') = mapAccumL (\(d,e) t -> let (t',d',e') = residualise' ls t fv d e
                                                                               in  ((d',e'),t')) (d,e) ts
                                    in  (Con c ts',d',e')
residualise' ls (Apply t u) fv d e = let (t',d',e') = residualise' ls t fv d e
                                         (u',d'',e'') = residualise' ls u fv d' e'
                                     in  (Apply t' u',d'',e'')
residualise' ls (Fun f) fv d e = (Fun f,d,e)
residualise' ls (Case t bs) fv d e = let (t',d',e') = residualise' ls t fv d e
                                         ((d'',e''),bs') = mapAccumL (\(d,e) (c,xs,t) -> let fv' = renameVars fv xs
                                                                                             xs' = take (length xs) fv'
                                                                                             (t',d',e') = residualise' ls (foldr concrete t xs') fv' d e
                                                                                         in  ((d',e'),(c,xs,foldl abstract t' xs'))) (d',e') bs
                                     in  (Case t' bs',d'',e'')
residualise' ls (Let x t u) fv d e = let x' = renameVar fv x
                                         (t',d',e') = residualise' ls t fv d e
                                         (u',d'',e'') = residualise' ls (concrete x' u) (x':fv) d' e'
                                     in  (subst t' (abstract u' x'),d'',e'')
residualise' ls t'@(Unfold l t u) fv d e = case [rename r u | (u,u') <- e, r <- funRenaming u' t'] of
                                              (t:ts) -> (t,d,e)
                                              [] -> case [rename r u' | (u,u') <- e, r <- funEmbedding u' t'] of
                                                       (t:ts) -> let (t'',s1,s2) = funGeneralise t t'
                                                                 in  residualise' ls (makeLet s2 t'') fv d e
                                                       [] -> let f = renameVar (fv ++ map fst d) "f"
                                                                 xs = free u
                                                                 t'' = foldl (\t x -> Apply t (Free x)) (Fun f) xs
                                                                 (u',d',e') = residualise' ((l,(t'',t)):ls) u (f:fv) d e
                                                             in  (t'',(f,(xs,foldl abstract u' xs)):d',(t'',t'):e')
residualise' ls (Fold l t) fv d e = case [instantiate s t' | (l',(t',u)) <- ls, l==l', s <- inst u t] of
                                       (t:ts) -> (t,d,e)
                                       [] -> residualise' ls t fv d e