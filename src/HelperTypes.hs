module HelperTypes where

import TermType
import LTSType
import Data.Maybe (fromMaybe)
import Debug.Trace (traceShow)
import Data.List (delete)

type FunctionDefinition = (String, ([String], Term))
type Generalization = (Term, LTS)

type Prog = (Term,[FunctionDefinition])

createLabels :: [String]
createLabels = map ((++) "#" . show) [1 ..]

renameVar :: Foldable t => t [Char] -> [Char] -> [Char]
renameVar fv x = if   x `elem` fv
                 then renameVar fv (x++"'")
                 else x            
renameVars fv xs = foldr (\x fv -> let x' = renameVar fv x in x':fv) fv xs                        

renameVarInLts :: LTS -> (String, String) -> LTS
renameVarInLts Leaf _ = Leaf
renameVarInLts (LTS (LTSTransitions e branches)) var = let
    e' = substituteTermWithNewVars e [var] 
    branches' = map (\(label, lts) -> (renameLabel label var, renameVarInLts lts var)) branches
    in LTS (LTSTransitions e' branches')

renameVarInLtsRecursively :: [(String, String)] -> LTS -> LTS
renameVarInLtsRecursively xs lts | traceShow ("in renameVarLtsRec, xs = " ++ show xs ++ ", lts = " ++ show lts) False = undefined
renameVarInLtsRecursively substitutions lts
  = foldl renameVarInLts lts substitutions

branchesSetsForConstructor :: [(Label, LTS)] -> [(Label, LTS)] -> Bool
branchesSetsForConstructor [] [] = True
branchesSetsForConstructor branches branches' = length branches == length branches' && all (\t -> tail (map fst t) == take (length t - 1) (map ConArg' createLabels)) [branches, branches']

branchesSetForConstructor :: [(Label, LTS)] -> Bool
branchesSetForConstructor [] = True
branchesSetForConstructor branch = tail (map fst branch) == take (length branch - 1) (map ConArg' createLabels)


matchCase :: [(Label, LTS)] -> [(Label, LTS)] -> Bool
matchCase bs bs' = length bs == length bs' && all (\((CaseBranch' c xs),(CaseBranch' c' xs')) 
    -> c == c' && length xs == length xs') (zip (map fst bs) (map fst bs'))

matchCase' bs bs' = length bs == length bs' && all (\((c,xs,t),(c',xs',t')) -> c == c' && length xs == length xs') (zip bs bs')

renameLabel :: Label -> (String, String) -> Label
renameLabel (X' x) (x', x'') = if x == x' then X' x'' else X' x
renameLabel u@(Lambda' x) (x', x'') = if x == x' then Lambda' x'' else u
renameLabel u@(ConArg' x) (x', x'') = if x == x' then ConArg' x'' else u
renameLabel u@(Unfold' x) (x', x'') = if x == x' then Unfold' x'' else u  
renameLabel u@(UnfoldCons' x) (x', x'') = if x == x' then UnfoldCons' x'' else u
renameLabel u@(LetX' x) (x', x'') = if x == x' then LetX' x'' else u
renameLabel (CaseBranch' x args) (x', x'') = let
    resultX = if x == x' then x'' else x
    resultArgs = map (\arg -> if arg == x' then x'' else arg) args 
    in CaseBranch' resultX resultArgs  
renameLabel u _ = u         
    
-- concrete function alternative
substituteTermWithNewVars :: Term -> [(String, String)] -> Term
substituteTermWithNewVars (Free x) pairs | traceShow ("in subs, x = " ++ x ++ ", pairs = " ++ show pairs) False = undefined
substituteTermWithNewVars (Free x) pairs = case lookup x pairs of
  Nothing -> Free x
  Just x' -> Free x'
substituteTermWithNewVars (Lambda x expr) xs = Lambda ("\\" ++ x) $ substituteTermWithNewVars expr xs
substituteTermWithNewVars (Apply term1 term2) xs =
  let term1' = substituteTermWithNewVars term1 xs
      term2' = substituteTermWithNewVars term2 xs
   in Apply term1' term2'
substituteTermWithNewVars (Case term branches) xs =
  let term' = substituteTermWithNewVars term xs  
      branches' = map (\(cons, vars, branchTerm) -> let
        vars' = map (\var -> fromMaybe var (lookup var xs)) vars
        in (cons, vars', substituteTermWithNewVars branchTerm xs)) branches
   in Case term' branches'
substituteTermWithNewVars (Let x term1 term2) xs =
  let term1' = substituteTermWithNewVars term1 xs
      term2' = substituteTermWithNewVars term2 xs
   in Let x term1' term2'
substituteTermWithNewVars (Con constructorName terms) xs =
  let terms' = map (`substituteTermWithNewVars` xs) terms
   in Con constructorName terms'
substituteTermWithNewVars (MultipleApply e0 funsDefs) xs =
  let e0' = substituteTermWithNewVars e0 xs
      funsDefs' =
        map
          ( \(funName, (args, term)) ->
              let renamedArgs = map (\t -> fromMaybe t (lookup t xs)) args
               in (funName, (renamedArgs, substituteTermWithNewVars term xs))
          )
          funsDefs
   in MultipleApply e0' funsDefs'
substituteTermWithNewVars fun _ = fun


substituteTermWithNewTerms :: Term -> [(String, Term)] -> Term
substituteTermWithNewTerms term xs | traceShow ("Substitute term with new terms " ++ show term ++ ";;;" ++ show xs) False = undefined
substituteTermWithNewTerms term xs = foldl substituteTermWithNewTerm term xs

substituteTermWithNewTerm :: Term -> (String, Term) -> Term
substituteTermWithNewTerm (Free x) (x', term') | x == x' = term'
                                               | otherwise = Free x
substituteTermWithNewTerm (Lambda x term) pair = Lambda x $ substituteTermWithNewTerm term pair
substituteTermWithNewTerm (Con con terms) pair = Con con $ map (\term -> substituteTermWithNewTerm term pair) terms
substituteTermWithNewTerm (Apply term' term'') pair = Apply (substituteTermWithNewTerm term' pair) $ substituteTermWithNewTerm term'' pair
substituteTermWithNewTerm (Case term branches) pair =
  Case (substituteTermWithNewTerm term pair) (map (\(name, args, term') -> (name, args,substituteTermWithNewTerm term' pair)) branches)
substituteTermWithNewTerm (Let x term term') pair = Let x (substituteTermWithNewTerm term pair) $ substituteTermWithNewTerm term' pair
substituteTermWithNewTerm term _ = term



-- is term t renaming of u
termRenaming :: Term -> Term -> [[(String, Term)]]
termRenaming t u | traceShow ("renaming: t = " ++ show t ++ ", u = " ++ show u) False = undefined
termRenaming t u = termRenaming' [] t u (free t ++ free u) [] []

termRenaming' :: t -> Term -> Term -> [String] -> [String] -> [(String, Term)] -> [[(String, Term)]]
termRenaming' fs (Free x) t fv bv s | x `elem` bv = [s | t==Free x]
termRenaming' fs (Lambda x t) (Lambda x' t') fv bv s = let x'' = renameVar fv x
                                               in  termRenaming' fs t t' (x'':fv) (x'':bv) s
termRenaming' fs (Con c ts) (Con c' ts') fv bv s | c==c' = foldr (\(t,t') ss -> concat [termRenaming' fs t t' fv bv s | s <- ss]) [s] (zip ts ts')
termRenaming' fs (Apply t u) (Apply t' u') fv bv s = concat [termRenaming' fs u u' fv bv s' | s' <- termRenaming' fs t t' fv bv s]
termRenaming' fs (Fun f) (Fun f') fv bv s | f==f' = [s]
termRenaming' fs (Case t bs) (Case t' bs') fv bv s | matchCase' bs bs' = foldr (\((c,xs,t),(c',xs',t')) ss -> let
        fv' = renameVars fv xs
        xs'' = take (length xs) fv'
    in  concat [termRenaming' fs t t' fv' (xs''++bv) s | s <- ss]) (termRenaming' fs t t' fv bv s) (zip bs bs')
termRenaming' fs (Let x t u) (Let x' t' u') fv bv s = let x'' = renameVar fv x
                                              in  concat [termRenaming' fs u u' (x'':fv) (x'':bv) s' | s' <- termRenaming' fs t t' fv bv s]
termRenaming' fs t u fv bv s | varApp fv t = let
                                            (Free x) = redex t
                                            xs = delete x (free t)
                                            u' = foldr Lambda u xs
                                         in  if   x `elem` map fst s
                                            then [s | (x,u') `elem` s]
                                            else [(x,u'):s]
termRenaming' fs t u fv bv s = []

varApp xs (Free x) = x `elem` xs
varApp xs (Apply t (Free x)) = varApp xs t
varApp xs t = False

redex (Case t bs) = redex t 
redex (Apply t u) = redex t
redex t = t