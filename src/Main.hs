module Main (
    main
) where

import Exception
import TermType
import Transformer
import Helpers
import HelperTypes
import Distiller

import Text.ParserCombinators.Parsec
import Debug.Trace
import System.Directory
import System.IO
import Control.Monad
import Data.List
import System.Exit
import System.Process

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
                                  Just (t,d) -> do
                                                putStrLn "Implementation needs revision"
                                                toplevel prog
                       Distill f -> case prog of
                                         Nothing -> do putStrLn "No program loaded"
                                                       toplevel prog
                                         Just (funsTerms, definitions) -> do
                                                       putStrLn "Implementation in progress"
                                                       p $ distillProg (funsTerms, definitions)
                                                       toplevel prog
                       Quit -> return ()
                       Help -> do putStrLn helpMessage
                                  toplevel prog
                       Unknown -> do putStrLn "Err: Could not parse command, type ':help' for a list of commands"
                                     toplevel prog