module TermType (createTermInContext, getTerm, getContext,
                Context (..), Term (..), TermInContext (..), place, free, bound) where

--import ProgPrinter
import Prelude hiding ((<>))
import Data.List


type TermInContext = (Term, Context)

createTermInContext :: Term -> Context -> TermInContext
createTermInContext term context = (term, context) 

getTerm :: TermInContext -> Term
getTerm (term, _) = term

getContext :: TermInContext -> Context
getContext (_, context) = context

data Term = Free String -- free variable
          | Lambda String Term -- lambda abstraction
          | Con String [Term] -- constructor application
          | Apply Term Term -- application
          | Fun String -- function call
          | Case Term [(String,[String],Term)] -- case expression
          | Let String Term Term -- let expression
          | MultipleApply Term [(String, ([String], Term))]
          deriving (Show, Ord)

-- equality of terms

instance Eq Term where
   (==) t t' = eqTerm (t,t')

eqTerm (Free x,Free x') = x==x'
eqTerm (Lambda x t,Lambda x' t') = eqTerm (t,t')
eqTerm (Con c ts,Con c' ts') | c==c' = all eqTerm (zip ts ts')
eqTerm (Apply t u,Apply t' u') = eqTerm (t,t') && eqTerm (u,u')
eqTerm (Fun f,Fun f') = f==f'
eqTerm (Case t bs,Case t' bs') | matchCase bs bs' = eqTerm (t,t') && all (\((_,_,t),(_,_,t')) -> eqTerm (t,t')) (zip bs bs')
eqTerm (Let x t u,Let x' t' u') = eqTerm (t,t') && eqTerm (u,u')
eqTerm (t,t') = False

data Context = EmptyCtx
             | ApplyCtx Context Term
             | CaseCtx Context [(String,[String],Term)] deriving Show


free t = nub (free' t)

free' (Free x) = [x]
free' (Lambda x t) = free' t
free' (Con c ts) = concatMap free' ts
free' (Apply t u)  = free' t ++ free' u
free' (Fun f) = []
free' (Case t bs) = free' t ++ concatMap (\(c,xs,t) -> free' t \\ xs) bs
free' (Let x t u) = free' t  ++ free' u

bound t = nub (bound' t)
bound' (Free x) = []
bound' (Lambda x t) = bound' t
bound' (Con c ts) = concatMap bound' ts
bound' (Apply t u) = bound' t ++ bound' u
bound' (Fun f) = [] 
bound' (Case t bs) = concatMap (\(c, xs, t') -> xs ++ bound' t') bs
bound' (Let x t u) = x : (bound' t ++ bound' u)

-- place term in context
place t EmptyCtx = t
place t (ApplyCtx con u) = place (Apply t u) con
place t (CaseCtx con bs) = place (Case t bs) con

matchCase bs bs' = length bs == length bs' && all (\((c,xs,t),(c',xs',t')) -> c == c' && length xs == length xs') (zip bs bs')