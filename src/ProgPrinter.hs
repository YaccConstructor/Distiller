module ProgPrinter where

import TermType
import Text.PrettyPrint.HughesPJ as P
import Prelude hiding ((<>))
import DistillationHelpers (renameVar, renameVars)
import LTSType (FunctionDefinition)

-- pretty printing

showProg :: (Term, [FunctionDefinition]) -> String
showProg p = renderStyle (Style { lineLength = 100, ribbonsPerLine = 1.1, mode = PageMode }) $ prettyProg p

stripLambda (Lambda x t) = let x' = renameVar (free t) x
                               (xs,u) = stripLambda t
                           in  (x':xs,u)
stripLambda t = ([],t)

blank = P.space

prettyCon t@(Con c ts)
   | isNat t   = int $ con2nat t
   | isList t  = brackets $ hcat $ punctuate comma $ map prettyTerm $ con2list t
   | null ts   = text c
   | otherwise = text c <> parens (hcat $ punctuate comma $ map prettyTerm ts)

prettyTerm (Free x) = text x
prettyTerm t@(Lambda _ _) = let (xs,t') = stripLambda t
                            in  text "\\" <> hsep (map text xs) <> text "." <> prettyTerm t'
prettyTerm t@(Con c ts) = prettyCon t
prettyTerm (Apply t u) = prettyTerm t <+> prettyAtom u
prettyTerm (Fun f) = text f
prettyTerm (Case t (b:bs)) = 
   hang (text "case" <+> prettyAtom t <+> text "of") 1 (blank <+> prettyBranch b $$ vcat (map ((text "|" <+>).prettyBranch) bs)) where
   prettyBranch (c,[],t) = text c <+> text "->" <+> prettyAtom t
   prettyBranch (c,xs,t) = text c <> parens(hcat $ punctuate comma $ map text xs) <+> text "->" <+> prettyAtom t $$ empty
prettyTerm (Let x t u) = let x' = renameVar (free u) x
                         in  (text "let" <+> text x' <+> text "=" <+> prettyTerm t) $$ (text "in" <+> prettyTerm u)

prettyAtom (Free x) = text x
prettyAtom t@(Con c ts) = prettyCon t
prettyAtom (Fun f) = text f
prettyAtom t = parens $ prettyTerm t

prettyProg (t,d) = let d' = [f | f <- d, fst f `elem` funs (t,d)]          
                   in  prettyEnv (("main",([],t)):d')


prettyEnv xs = vcat (punctuate semi $ map (\(f,(xs,t)) -> text f <+> hsep (map text xs) <+> equals <+> prettyTerm t) xs)

funs (t,d) = funs' d t []

funs' d (Free x) fs = fs
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

isList (Con "Nil" []) = True
isList (Con "Cons" [h,t]) = isList t
isList _ = False

list2con [] = Con "Nil" []
list2con (h:t) = Con "Cons" [h,list2con t]

con2list (Con "Nil" [])  = []
con2list (Con "Cons" [h,t]) = h:con2list t

range2con m n = if    m > n 
                then Con "Nil" []
                else Con "Cons" [nat2con m,range2con (m+1) n]

isNat (Con "Zero" []) = True
isNat (Con "Succ" [n]) = isNat n
isNat _ = False

nat2con 0 = Con "Zero" []
nat2con n = Con "Succ" [nat2con $ n-1]

con2nat (Con "Zero" [])  = 0
con2nat (Con "Succ" [n]) = 1+con2nat n