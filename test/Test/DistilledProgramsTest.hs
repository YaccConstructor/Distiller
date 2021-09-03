{-# LANGUAGE InstanceSigs #-}

module Test.DistilledProgramsTest where

import qualified Test.Tasty.Hedgehog
import qualified Hedgehog.Gen as Gen
import Hedgehog
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.HUnit

import Test.Generators
import Test.TestHelpers
import Term
import Trans (dist)
import Helpers

import Control.Exception
import Text.Printf (printf)
import Data.Maybe (fromJust, isJust)


createTest :: String -> String -> ((Term, [(String, ([String], Term))]) -> (Term, [(String, ([String], Term))]) -> Property) -> p -> IO TestTree
createTest fileToDistill importsForDistill makePropertyTest timeoutForDistillation =  do
  progToDistill <- load fileToDistill importsForDistill  
  if isJust progToDistill
  then do
    distillationResult <- try (evaluate $ dist (fromJust progToDistill)) :: IO (Either SomeException (Term, [(String, ([String], Term))]))
    case distillationResult of
      Left ex -> do 
        let testCaseName = printf "Distillation of %s" fileToDistill
        let assertion = assertFailure $ printf "program: %s; imports: %s; exception: %s" fileToDistill importsForDistill (show ex)
        return $ testCase testCaseName assertion
      Right  distilled -> do
        let testCaseName = printf "%s: evaluation results of original and distilled versions are equal." fileToDistill 
        return $ testProperty testCaseName $ makePropertyTest (fromJust progToDistill) distilled
  else do
    let testCaseName = printf "Parsing: %s" fileToDistill
    let assertion = assertFailure $ printf "program: %s; imports: %s." fileToDistill importsForDistill
    return $ testCase testCaseName assertion


test_plusMinus_2_property :: IO TestTree
test_plusMinus_2_property = do
    let plusMinus_2 (origMainTerm, origTerms) (distilledMainTerm, distilledTerms) =     
         property $ do  n <- forAll genNat
                        m <- forAll genNat
                        let n_term = natToTerm n
                        let m_term = natToTerm m
                        let (origRes,origReductions,origAlloc) = Term.eval (subst m_term (abstract (subst n_term (abstract origMainTerm "n")) "m")) EmptyCtx origTerms 0 0
                        let (distilledRes, distilledReductions, distilledAlloc) = Term.eval (subst m_term (abstract (subst n_term (abstract distilledMainTerm "n")) "m")) EmptyCtx distilledTerms 0 0
                        origRes === distilledRes
    
    createTest "plusMinus_2" "inputs/" plusMinus_2 defaultTimeout 
    