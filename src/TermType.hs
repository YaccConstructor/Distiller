module TermType (createTermInContext, getTerm, getContext,
                Context, Term (..)) where

--import ProgPrinter
import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ as P
import Text.ParserCombinators.Parsec hiding (labels)
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language


type TermInContext = (Term, Context)

createTermInContext :: Term -> Context -> TermInContext
createTermInContext term context = (term, context) 

getTerm :: TermInContext -> Term
getTerm (term, _) = term

getContext :: TermInContext -> Context
getContext (_, context) = context

data Term = Free String -- free variable
--          | Bound Int -- bound variable with de Bruijn index
          | Lambda String Term -- lambda abstraction
          | Con String [Term] -- constructor application
          | Apply Term Term -- application
          | Fun String -- function call
          | Case Term [(String,[String],Term)] -- case expression
          | Let String Term Term -- let expression
          | MultipleApply Term [(String, ([String], Term))]
--          | Unfold String Term Term -- unfolding
--          | Fold String Term -- folding
--          | Gen Term Term -- generalization node
          deriving Show

-- equality of terms

instance Eq Term where
   (==) t t' = eqTerm (t,t')

eqTerm (Free x,Free x') = x==x'
--eqTerm (Bound i,Bound i') = i==i'
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

-- place term in context

place t EmptyCtx = t
place t (ApplyCtx con u) = place (Apply t u) con
place t (CaseCtx con bs) = place (Case t bs) con

matchCase bs bs' = length bs == length bs' && all (\((c,xs,t),(c',xs',t')) -> c == c' && length xs == length xs') (zip bs bs')

-- term instance

inst t u = inst' t u []

inst' (Free x) t s = if   x `elem` map fst s
                     then [s | (x,t) `elem` s]
                     else [(x,t):s]
--inst' (Bound i) (Bound i') s | i==i' = [s]
inst' (Lambda x t) (Lambda x' t') s = inst' t t' s
inst' (Con c ts) (Con c' ts') s | c==c' = foldr (\(t,t') ss -> concat [inst' t t' s | s <- ss]) [s] (zip ts ts')
inst' (Apply t u) (Apply t' u') s = concat [inst' u u' s' | s' <- inst' t t' s]
inst' (Fun f) (Fun f') s | f==f' = [s]
inst' (Case t bs) (Case t' bs') s | matchCase bs bs' = foldr (\((c,xs,t),(c',xs',t')) ss -> concat [inst' t t' s | s <- ss]) (inst' t t' s) (zip bs bs')
inst' (Let x t u) (Let x' t' u') s = concat [inst' u u' s' | s' <- inst' t t' s]
inst' t t' s = []