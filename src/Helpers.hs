module Helpers where

import TermType
import ProgParser

import System.Directory

{--evalProg :: (Num c, Foldable t) => [[Char]] -> Term -> [(String, (t String, Term))] -> IO (Term, Int, c)
evalProg [] t d = do let (v,r,a) = eval t EmptyCtx d 0 0
                     return (v, r, a)
evalProg (x:xs) t d = do putStr (x ++ " = ")
                         hFlush stdout
                         l <-  getLine
                         case parseTerm l of
                            Left s -> do putStrLn ("Could not parse term: " ++ show s)
                                         evalProg (x:xs) t d
                            Right u -> evalProg xs (subst u (abstract t x)) d-}


-- return (result of function = Term,  : [(function name, ([arguments], the same Term) )]
loadProg :: [String] -> [String] -> [(String, ([String], Term))] -> Maybe String -> IO (Maybe (Term, [(String, ([String], Term))]))
loadProg [] _ funDefinitions _ = return (Just (makeProg funDefinitions))
loadProg (i:importFiles) loadedImportFiles funDefinitions sourcesDir = do
  if  i `elem` loadedImportFiles
    then loadProg importFiles loadedImportFiles funDefinitions sourcesDir
    else case sourcesDir of
        Nothing -> do
              fileContent <- loadFile i
              case fileContent of
                 Nothing -> return Nothing
                 Just (importFiles',funDefinitions') -> loadProg (importFiles++importFiles') (i:loadedImportFiles) (funDefinitions++funDefinitions') sourcesDir
        Just sourcesDir' -> do
              r <- loadFile (sourcesDir' ++ i)
              case r of
                 Nothing -> return Nothing
                 Just (fs,d') -> loadProg (importFiles++fs) (i:loadedImportFiles) (funDefinitions++d') sourcesDir

loadFile :: String -> IO (Maybe ([String],[(String,([String],Term))]))
loadFile f = do x <-  doesFileExist (f++".pot")
                if   x
                     then do putStrLn ("Loading file: "++f++".pot")
                             c <-  readFile (f++".pot")
                             case parseModule c of
                                Left s -> do putStrLn ("Could not parse program in file "++f++".pot: "++ show s)
                                             return Nothing
                                Right t -> return (Just t)
                     else do putStrLn ("No such file: "++f++".pot")
                             return Nothing