module HomeomorphicEmbeddingChecker (isRenaming, isHomeomorphicEmbedding) where


import TermType
import LTSType
import HelperTypes

isRenaming :: LTS -> LTS -> [(String, String)]
isRenaming lts1 lts2 = isRenaming' [] lts1 lts2 [] [] []

isRenaming' :: [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [(String, String)]
isRenaming' funNamesAccum (LTS (LTSTransitions t@(Free x) _))
                          (LTS (LTSTransitions t'@(Free x') _)) freeVars boundVars renaming
    | x `elem` freeVars && t' == t = renaming
    | x `elem` freeVars = []
    | x `elem` boundVars = if x `elem` map fst renaming
        then if (x,x') `elem` renaming
            then renaming
            else (x,x') : renaming
        else []
-- unfold        
isRenaming' funNamesAccum (LTS (LTSTransitions _ [('*' : funName, t)]))
                          (LTS (LTSTransitions _ [('*' : funName', t')])) freeVars boundVars renaming = 
    if (funName, funName') `elem` funNamesAccum
        then renaming
        else isRenaming' ((funName, funName') : funNamesAccum) t t' freeVars boundVars renaming
-- lambda        
isRenaming' funNamesAccum (LTS (LTSTransitions _ [('\\' : x, t)]))
                          (LTS (LTSTransitions _ [('\\' : x', t')])) freeVars boundVars renaming = let 
        x'' = renameVar freeVars x
        in isRenaming' funNamesAccum t t' (x'' : freeVars) boundVars renaming
-- constructor             
isRenaming' funNamesAccum (LTS (LTSTransitions _ bs@((conName, Leaf) : branches)))
                          (LTS (LTSTransitions _ bs'@((conName', Leaf) : branches'))) freeVars boundVars renaming
    | branchesForConstructor bs bs' = 
      if conName == conName' then let
        termPairs = zip (map snd branches) (map snd branches')
        in foldr (\(t, t') renaming' -> renaming' ++ isRenaming' funNamesAccum t t' freeVars boundVars renaming') renaming termPairs
        else []
-- Apply                
isRenaming' funNamesAccum  (LTS (LTSTransitions _ [("@", t), ("#1", u)])) 
                           (LTS (LTSTransitions _ [("@", t'), ("#1", u')])) freeVars boundVars renaming = let
    a = isRenaming' funNamesAccum t t' freeVars boundVars renaming
    b = isRenaming' funNamesAccum u u' freeVars boundVars a in b
-- let            
isRenaming' funNamesAccum (LTS (LTSTransitions _ [("let", t), (x, u)])) 
                          (LTS (LTSTransitions _ [("let", t'), (x', u')])) freeVars boundVars renaming = let
    x'' = renameVar freeVars x
    a = isRenaming' funNamesAccum t t' freeVars boundVars renaming
    b = isRenaming' funNamesAccum u u' (x'' : freeVars) (x'' : boundVars) a in b
-- case      
isRenaming' funNamesAccum (LTS (LTSTransitions' _ (("case", [], t) : branches)))
                          (LTS (LTSTransitions' _ (("case", [], t') : branches'))) freeVars boundVars renaming
    | matchCase branches branches' = let
        initializer = isRenaming' funNamesAccum t t' freeVars boundVars renaming 
        branchess = zip branches branches'
        in foldr (\((c, xs, u), (c', xs', u')) renaming' -> let 
            freeVars' = renameVars freeVars xs
            xs'' = take (length xs) freeVars'
            in isRenaming' funNamesAccum u u' freeVars' (xs'' ++ boundVars) renaming') initializer branchess
isRenaming' _ _ _ _ _ _ = []                                                                       
   
isHomeomorphicEmbedding :: LTS -> LTS -> [(String, String)]
isHomeomorphicEmbedding lts1 lts2 = coupled [] lts1 lts2 [] [] []

embed ::  [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [(String, String)]
embed funNamesAccum lts1 lts2 freeVars boundVars renaming =
  dived funNamesAccum lts1 lts2 freeVars boundVars renaming ++ coupled funNamesAccum lts1 lts2 freeVars boundVars renaming

dived ::  [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [(String, String)]
dived funNamesAccum lts1@(LTS (LTSTransitions _ branches)) lts2@(LTS (LTSTransitions _ branches')) freeVars boundVars renaming =
    -- if some i has embedding, than dived is passed
    concatMap (\(t, t') -> embed funNamesAccum t t' freeVars boundVars renaming)
    $ zip (map snd branches) (map snd branches')

-- if all i has embedding, than coupled is passed
coupled :: [(String, String)] -> LTS -> LTS -> [String] -> [String] -> [(String, String)] -> [(String, String)]
coupled funNamedAccum (LTS (LTSTransitions t@(Free x) _))
                      (LTS (LTSTransitions t'@(Free x') _)) freeVars boundVars renaming
    | x `elem` freeVars && t' == t = renaming
    | x `elem` freeVars = []
    | x `elem` boundVars = if x `elem` map fst renaming
        then if (x,x') `elem` renaming
            then renaming
            else (x,x') : renaming
        else []
-- unfold    
coupled funNamesAccum (LTS (LTSTransitions _ [('*' : funName, t)]))
                      (LTS (LTSTransitions _ [('*' : funName', t')])) freeVars boundVars renaming 
         | (funName, funName') `elem` funNamesAccum = renaming
         | otherwise = embed ((funName, funName') : funNamesAccum) t t' freeVars boundVars renaming
-- lambda           
coupled funNamesAccum (LTS (LTSTransitions _ [('\\' : x, t)]))
                          (LTS (LTSTransitions _ [('\\' : x', t')])) freeVars boundVars renaming = let 
        x'' = renameVar freeVars x
        in embed funNamesAccum t t' (x'' : freeVars) boundVars renaming
-- constructor             
coupled funNamesAccum (LTS (LTSTransitions _ bs@((conName, Leaf) : branches)))
                          (LTS (LTSTransitions _ bs'@((conName', Leaf) : branches'))) freeVars boundVars renaming
    | branchesForConstructor bs bs' = 
      if conName == conName' then let
        termPairs = zip (map snd branches) (map snd branches')
        in foldr (\(t, t') renaming' -> renaming' ++ embed funNamesAccum t t' freeVars boundVars renaming') renaming termPairs
        else []
-- Apply                
coupled funNamesAccum  (LTS (LTSTransitions _ [("@", t), ("#1", u)])) 
                           (LTS (LTSTransitions _ [("@", t'), ("#1", u')])) freeVars boundVars renaming = let
    a = embed funNamesAccum t t' freeVars boundVars renaming
    b = embed funNamesAccum u u' freeVars boundVars a in b
-- let            
coupled funNamesAccum (LTS (LTSTransitions _ [("let", t), (x, u)])) 
                          (LTS (LTSTransitions _ [("let", t'), (x', u')])) freeVars boundVars renaming = let
    x'' = renameVar freeVars x
    a = embed funNamesAccum t t' freeVars boundVars renaming
    b = embed funNamesAccum u u' (x'' : freeVars) (x'' : boundVars) a in b
-- case      
coupled funNamesAccum (LTS (LTSTransitions' _ (("case", [], t) : branches)))
                          (LTS (LTSTransitions' _ (("case", [], t') : branches'))) freeVars boundVars renaming
    | matchCase branches branches' = let
        initializer = embed funNamesAccum t t' freeVars boundVars renaming 
        branchess = zip branches branches'
        in foldr (\((c, xs, u), (c', xs', u')) renaming' -> let 
            freeVars' = renameVars freeVars xs
            xs'' = take (length xs) freeVars'
            in embed funNamesAccum u u' freeVars' (xs'' ++ boundVars) renaming') initializer branchess
coupled _ _ _ _ _ _ = []                                                                        
         
