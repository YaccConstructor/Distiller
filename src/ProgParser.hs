module ProgParser where

import TermType
import Generalizer
import ProgPrinter

import Data.List

import Text.ParserCombinators.Parsec hiding (labels)
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

-- lexing and parsing

potDef = emptyDef
         { commentStart    = "/*"
         , commentEnd      = "*/"
         , commentLine     = "--"
         , nestedComments  = True
         , identStart      = lower
         , identLetter     = letter <|> digit <|> oneOf "_'"
         , reservedNames   = ["import", "case","of","let","in","letrec","ALL","EX","ANY"]
         , reservedOpNames = ["~","/\\","\\/","<=>","=>"]
         , caseSensitive   = True
         }

lexer = T.makeTokenParser potDef

symbol     = T.symbol lexer
bracks     = T.parens lexer
semic      = T.semi lexer
comm       = T.comma lexer
identifier = T.identifier lexer
reserved   = T.reserved lexer
reservedOp = T.reservedOp lexer
natural    = T.natural lexer

con = do
      c <- upper
      cs <- many letter
      spaces
      return (c:cs)

makeProg :: [(String, ([String], Term))] -> (Term, [(String, ([String], Term))])
makeProg funDefinitions = let
                        funsNames = map fst funDefinitions
                        funDefinitions' =  map (\(funName,(funFreeVariables, funResultTerm)) ->
                            (funName,(funFreeVariables, makeFun funsNames funResultTerm))) funDefinitions
              in  case lookup "main" funDefinitions' of
                     Nothing -> error "No main function"
                     Just (mainName,t) -> (t,delete ("main",(mainName,t)) funDefinitions')

-- check if term name is same as function name
makeFun :: [String] -> Term -> Term
makeFun funNames (Free x) = if x `elem` funNames then Fun x else Free x
makeFun _ (Bound i) = Bound i
makeFun funNames (Lambda x t) = Lambda x (makeFun funNames t)
makeFun funNames (Con c ts) = Con c (map (makeFun funNames) ts)
makeFun funNames (Apply t u) = Apply (makeFun funNames t) (makeFun funNames u)
makeFun _ (Fun f) = Fun f
makeFun funNames (Case t bs) = Case (makeFun funNames t) (map (\(c,xs,t) -> (c,xs,makeFun funNames t)) bs)
makeFun funNames (Let x t u) = Let x (makeFun funNames t) (makeFun funNames u)

modul = do
        fs <- many imp
        ds <- sepBy1 fundef semic
        return (fs,ds)

imp = do
      reserved "import"
      con

fundef = do
         f <- identifier
         xs <- many identifier
         symbol "="
         e <- term
         return (f,(xs,e))

term =     do
           a <- atom
           as <- many atom
           return (foldl Apply a as)
       <|> do
           symbol "\\"
           xs <- many1 identifier
           symbol "->"
           t <- term
           return (foldr (\x t->Lambda x t {-(abstract t x)-}) t xs)
       <|> do
           reserved "case"
           t <- term
           reserved "of"
           bs <- sepBy1 branch (symbol "|")
           return (Case t bs)
      <|> do
          reserved "let"
          x <- identifier
          symbol "="
          t <- term
          reserved "in"
          u <- term
          return (Let x t u{-(abstract u x)-})

atom =     do Free <$> identifier
       <|> do
           c <- con
           ts <- option [] (bracks (sepBy1 term comm))
           return (Con c ts) 
       <|> do 
           m <- natural
           option (nat2con m) (do symbol ".." 
                                  range2con m <$> natural)
       <|> do
           symbol "["
           ts <- sepBy term comm
           symbol "]"
           return (list2con ts)
       <|> bracks term

branch = do
         c <- con
         xs <- option [] (bracks (sepBy1 identifier comm))
         symbol "->"
         t <- term
         return (c,xs,t)

parseTerm = parse term "Parse error"

-- return ([imports], fundef : [(function name, ([arguments], Term) )]
parseModule :: String -> Either ParseError ([String], [(String, ([String], Term))])
parseModule = parse modul "Parse error"