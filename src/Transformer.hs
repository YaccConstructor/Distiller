module Transformer (transform) where

import TermType
import LTSType
import HelperTypes

-- concrete function alternative
substituteTermWithNewVars :: Term -> [String] -> Term
substituteTermWithNewVars (Free _) [x'] = Free x'
substituteTermWithNewVars (Free _) _ = error "Constructor Free has arity 1, but got more variables."
substituteTermWithNewVars (Lambda x expr) xs = Lambda x $ substituteTermWithNewVars expr xs
substituteTermWithNewVars (Apply term1 term2) xs = let
    term1' = substituteTermWithNewVars term1 xs
    term2' = substituteTermWithNewVars term2 xs
    in Apply term1' term2'
substituteTermWithNewVars (Case term branches) xs = let
    term' = substituteTermWithNewVars term xs
    branches' = map (\(cons, vars, branchTerm) -> (cons, vars, substituteTermWithNewVars branchTerm xs)) branches
    in Case term' branches'
substituteTermWithNewVars (Let x term1 term2) xs = let
    term1' = substituteTermWithNewVars term1 xs
    term2' = substituteTermWithNewVars term2 xs
    in Let x term1' term2'    
substituteTermWithNewVars (Con constructorName terms) xs = let
    terms' = map (`substituteTermWithNewVars` xs) terms
    in Con constructorName terms'     
substituteTermWithNewVars (MultipleApply e0 funsDefs) xs = let
    e0' = substituteTermWithNewVars e0 xs
    funsDefs' = map (\(funName,(args,term)) -> (funName, (args, substituteTermWithNewVars term xs))) funsDefs
    in MultipleApply e0' funsDefs'    
substituteTermWithNewVars fun xs = fun         
    
    

substituteTermWithNewTerms :: Term -> [Term] -> Term
substituteTermWithNewTerms term _ = term



transform :: Int ->  TermInContext -> [String] -> [Generalization] -> [FunctionDefinition] -> LTS
transform index termInContext funNamesAccum previousGensAccum funsDefs = doLTS0Tr
transform index termInContext funNamesAccum previousGensAccum funsDefs = doLTS0Tr

transform' :: Int -> LTS -> Context -> [String] -> [Generalization] -> [FunctionDefinition] -> LTS
transform' index lts EmptyCtx _ _ _ = lts
transform' index t@(LTS lts) (ApplyCtx context expr) funNames previousGensAccum funsDefs = let
    term = getOldTerm lts
    newLts = updateLTS t "@" (transform index (expr, EmptyCtx) funNames previousGensAccum funsDefs) "#1" (Apply term expr)  
    in transform' index newLts context funNames previousGensAccum funsDefs
transform' index t@(LTS lts) (CaseCtx context branches) funsNames previousGens funsDefs = let
    root = Case (getOldTerm lts) branches
    firstBranch = ("case", t)
    otherBranches = map (\(branchName, _, resultTerm) -> (branchName, transform index (resultTerm, context) funsNames previousGens funsDefs)) branches
    in doLTSManyTr root $ firstBranch : otherBranches 
--transform' [x -> (x, 0)]
transform' index t@(LTS (LTSTransitions term@(Free x) [(xLabel, doLTS0Tr)])) (CaseCtx context branches) funsNames previousGens funsDefs = 
    if x == xLabel 
        then let
            root = Case term branches
            firstBranch = ("case", t)
            otherBranches = map (\(branchName, args, resultTerm) -> let
                resultTerm' = substituteTermWithNewVars resultTerm args
                transformedTerm = transform index (resultTerm', context) funsNames previousGens funsDefs
                in (branchName, transformedTerm)) branches
            in doLTSManyTr root $ firstBranch : otherBranches
        else error "Error: got branch x -> (x,0), but label is not the same as x"
transform' _ _ _ _ _ _ = error "Got error trying to transform."    
  


-- level n transformer

{--trans 0 t k fv m d e = return (place t k)

trans n (Free x) (CaseCtx k bs) fv m d e = do
                                           bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                         fv' = renameVars fv xs
                                                                         xs' = take (length xs) fv'
                                                                         u = foldr concrete (subst (Con c (map Free xs')) (abstract t' x)) xs'
                                                                     in do
                                                                        u' <- trans n u EmptyCtx fv' m d e
                                                                        return (c,xs,foldl abstract u' xs')) bs
                                           return (Case (Free x) bs')
trans n (Free x) k fv m d e = transCtx n (Free x) k fv m d e
trans n (Lambda x t) EmptyCtx fv m d e = let x' = renameVar fv x
                                         in do
                                            t' <- trans n (concrete x' t) EmptyCtx (x':fv) m d e
                                            return (Lambda x (abstract t' x'))
trans n (Lambda x t) (ApplyCtx k u) fv m d e = trans n (subst u t) k fv m d e
trans n (Lambda x t) (CaseCtx k bs) fv m d e = error "Unapplied function in case selector"
trans n (Con c ts) EmptyCtx fv m d e = do
                                       ts' <- mapM (\t -> trans n t EmptyCtx fv m d e) ts
                                       return (Con c ts')
trans n (Con c ts) (ApplyCtx k u) fv m d e = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
trans n (Con c ts) (CaseCtx k bs) fv m d e = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                                Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                                Just (c',xs,t) -> trans n (foldr subst t ts) k fv m d e
trans n (Apply t u) k fv m d e = trans n t (ApplyCtx k u) fv m d e
trans n (Fun f) k fv m d e = let t = returnval (trans (n-1) (Fun f) k fv [] d e)
                                 (t',d',e') = residualise t d e
                              in  case [(l,u,s) | (l,u) <- m, s <- inst u t'] of
                                     ((l,u,s):ls) -> do
                                                     s' <- mapM (\(x,t) -> do
                                                                           t' <- trans n t EmptyCtx fv m d e
                                                                           return (x,t')) s
                                                     return (makeLet' s' (Fold l u))
                                     [] -> case [l | (l,u) <- m, isEmbedding u t'] of
                                              (l:ls) -> throw (l,t')
                                              [] -> let l = renameVar (map fst m) "l"
                                                        handler (l',u) = if   l==l'
                                                                         then let (u',s1,s2) = generaliseTerm t' u
                                                                              in  trans n (makeLet s1 u') EmptyCtx fv m d' e'
                                                                         else throw (l',u)
                                                    in  do
                                                       u <- handle (trans n (unfold(t',d')) EmptyCtx fv ((l,t'):m) d' e') handler
                                                        return (if l `elem` folds u then Unfold l t' u else u)
trans n (Case t bs) k fv m d e = trans n t (CaseCtx k bs) fv m d e
trans n (Let x t u) k fv m d e = let x' = renameVar fv x
                                 in do
                                    t' <- trans n t EmptyCtx fv m d e
                                    u' <- trans n (concrete x' u) k (x':fv) m d e
                                    return (Let x t' (abstract u' x'))

transCtx n t EmptyCtx fv m d e = return t
transCtx n t (ApplyCtx k u) fv m d e = do
                                       u' <- trans n u EmptyCtx fv m d e
                                       transCtx n (Apply t u') k fv m d e
transCtx n t (CaseCtx k bs) fv m d e = do
                                       bs' <- mapM (\(c,xs,t) -> let fv' = renameVars fv xs
                                                                     xs' = take (length xs) fv'
                                                                 in do
                                                                    t' <- trans n (foldr concrete t xs') k fv' m d e
                                                                    return (c,xs,foldl abstract t' xs')) bs
                                       return (Case t bs')--}