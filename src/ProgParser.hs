module ProgParser where

-- lexing and parsing

{--potDef = emptyDef
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

makeProg ds = let fs = map fst ds
                  ds' =  map (\(f,(xs,t)) -> (f,(xs,foldl abstract (makeFun fs t) xs))) ds
              in  case lookup "main" ds' of
                     Nothing -> error "No main function"
                     Just (xs,t) -> (t,delete ("main",(xs,t)) ds')

makeFun fs (Free x) = if x `elem` fs then Fun x else Free x
makeFun fs (Bound i) = Bound i
makeFun fs (Lambda x t) = Lambda x (makeFun fs t)
makeFun fs (Con c ts) = Con c (map (makeFun fs) ts)
makeFun fs (Apply t u) = Apply (makeFun fs t) (makeFun fs u)
makeFun fs (Fun f) = Fun f
makeFun fs (Case t bs) = Case (makeFun fs t) (map (\(c,xs,t) -> (c,xs,makeFun fs t)) bs)
makeFun fs (Let x t u) = Let x (makeFun fs t) (makeFun fs u)

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
           return (foldr (\x t->Lambda x (abstract t x)) t xs)
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
          return (Let x t (abstract u x))

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
         return (c,xs,foldl abstract t xs)

parseTerm = parse term "Parse error"

parseModule :: String -> Either ParseError ([[Char]], [(String, ([String], Term))])
parseModule = parse modul "Parse error"
--}