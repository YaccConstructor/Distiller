module Main (
    main
) where

import TermType
import ExecutionHelpers
import LTSType
import Distiller
import ProgPrinter
import Evaluator
import DistillationHelpers
import ProgParser

import System.IO

data Command = Load String (Maybe String)
             | Prog
             | Term
             | Eval
             | Distill (Maybe String)
             | Quit
             | Help
             | Unknown

command str = let res = words str
              in case res of
                   [":load",f] -> Load f Nothing
                   [":load",f, sourceDir] -> Load f (Just sourceDir)
                   [":prog"] -> Prog
                   [":term"] -> Term
                   [":eval"] -> Eval
                   [":distill"] -> Distill Nothing
                   [":distill", f] -> Distill (Just f)
                   [":quit"] -> Quit
                   [":help"] -> Help
                   _ -> Unknown

helpMessage = "\n:load filename <directory>\t\tTo load the given filename. If a directory is provided, then imports will be loaded from the specified directory. Else all imports will be loaded from the current directory.\n"++
               ":prog\t\t\tTo print the current program\n"++
               ":term\t\t\tTo print the current term\n"++
               ":eval\t\t\tTo evaluate the current program\n"++
               ":distill <filename>\t\tTo distill the current program. If the file name is provided, the distillation result will be stored in the specified file.\n"++
               ":quit\t\t\tTo quit\n"++
               ":help\t\t\tTo print this message\n"


-- Entry point for main program

main = toplevel Nothing

toplevel :: Maybe Prog -> IO ()
toplevel prog = do 
                    putStr "POT> "
                    hFlush stdout
                    x <-  getLine
                    case command x of
                       Load f sourcesDir -> do
                         prog <- loadProg [f] [] [] sourcesDir
                         toplevel prog
                       Prog -> case prog of
                                  Nothing -> do putStrLn "No program loaded"
                                                toplevel prog
                                  Just (t,d) -> do print (t,d)
                                                   toplevel prog
                       Term -> case prog of
                                  Nothing -> do putStrLn "No program loaded"
                                                toplevel prog
                                  Just (t,d) -> do print t 
                                                   toplevel prog
                       Eval -> case prog of
                                  Nothing -> do putStrLn "No program loaded"
                                                toplevel prog
                                  Just (t,d) -> f (free t) t
                                                                             where
                                                                             f [] t = do let (v,r,a) = eval t EmptyCtx d 0 0
                                                                                         print v
                                                                                         putStrLn ("Reductions: " ++ show r)
                                                                                         putStrLn ("Allocations: " ++ show a)
                                                                                         toplevel prog
                                                                             f (x:xs) t = do putStr (x++" = ")
                                                                                             hFlush stdout
                                                                                             l <-  getLine
                                                                                             case parseTerm l of
                                                                                                Left s -> do putStrLn ("Could not parse term: "++ show s)
                                                                                                             f (x:xs) t
                                                                                                Right u -> f xs (substituteTermWithNewTerm u (x, t)) 
                       Distill f -> case prog of
                                         Nothing -> do putStrLn "No program loaded"
                                                       toplevel prog
                                         Just (funsTerms, definitions) -> do
                                                       let p = distillProg (funsTerms, definitions)
                                                       print p
                                                       case f of
                                                          Nothing -> putStrLn (showProg p)
                                                          Just f -> do
                                                             putStrLn (showProg p)
                                                             writeFile f (showProg p)
                                                       toplevel prog
                       Quit -> return ()
                       Help -> do putStrLn helpMessage
                                  toplevel prog
                       Unknown -> do putStrLn "Err: Could not parse command, type ':help' for a list of commands"
                                     toplevel prog