module Driver where

import TermType


-- convert term to process tree
process (Free x) args fv m d = Free x
process (Bound i) args fv m d = Bound i
process (Lambda x t) args fv m d = let x' = renameVar fv x
                                       t' = process (concrete x' t) args (x':fv) m d
                                   in  Lambda x (abstract t' x')
process (Con c ts) args fv m d = Con c (map (\t -> process t args fv m d) ts)
process (Apply t (Free x)) args fv m d = process t (Free x:args) fv m d
process (Apply t u) args fv m d = let x = renameVar fv "x"
                                      t' = process t (Free x:args) (x:fv) m d
                                      u' = process u [] fv m d
                                  in  Let x u' (abstract t' x)
process (Fun f) args fv m d = let t = foldl Apply (Fun f) args
                              in  case lookup f m of
                                     Just l ->  Fold l t
                                     Nothing -> case lookup f d of
                                                   Nothing -> error ("Undefined function: "++f)
                                                   Just (xs,u) -> let l = renameVar (map snd m) "l"
                                                                      t' = process (foldr subst u args) [] fv ((f,l):m) d
                                                                  in  if l `elem` folds t' then Unfold l t t' else t'
process (Case (Free x) bs) args fv m d = let bs' = map (\(c,xs,t) -> let fv' = renameVars fv xs
                                                                         xs' = take (length xs) fv'
                                                                         t' = process (foldr concrete t xs') args fv' m d
                                                                     in (c,xs,foldl abstract t' xs')) bs
                                         in  Case (Free x) bs'
process (Case t bs) args fv m d = let x = renameVar fv "x"
                                      t' = process t [] fv m d
                                      bs' = map (\(c,xs,t) -> let fv' = renameVars fv xs
                                                                  xs' = take (length xs) fv'
                                                                  t' = process (foldr concrete t xs') args fv' m d
                                                              in (c,xs,foldl abstract t' xs')) bs
                                  in  Let x t' (abstract (Case (Free x) bs') x)
process (Let x t u) args fv m d = let x' = renameVar fv x
                                      t' = process t [] fv m d
                                      u' = process (concrete x' u) args (x':fv) m d
                                  in Let x t' (abstract u' x')

processFun d (f,(xs,t)) = let t = foldl (\t x -> Apply t (Free x)) (Fun f) xs
                          in  (t,process t [] xs [] d)
