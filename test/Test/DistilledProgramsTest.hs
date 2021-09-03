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

substituteAll :: Foldable t => Term -> t (String, Term) -> Term
substituteAll =
    foldl (\ term (name, subst_term) -> subst subst_term (abstract term name)) 

getEvalResults :: (Num a1, Foldable t1, Num a2, Foldable t3, Foldable t2) =>
                  t2 (String, Term)
                  -> (Term, [(String, (t3 String, Term))])
                  -> (Term, [(String, (t1 String, Term))])
                  -> ((Term, Int, a2), (Term, Int, a1))
getEvalResults substitutions (origMainTerm, origTerms) (distilledMainTerm, distilledTerms) =         
    let origResults = Term.eval (substituteAll origMainTerm substitutions) EmptyCtx origTerms 0 0            
        distilledResults = Term.eval (substituteAll distilledMainTerm substitutions)  EmptyCtx distilledTerms 0 0
    in (origResults, distilledResults)

createTest :: String 
              -> String 
              -> ((Term, [(String, ([String], Term))]) -> (Term, [(String, ([String], Term))]) -> (Property, Property)) 
              -> p 
              -> IO TestTree
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
        let (distillerIsCorrect, distillerIsOptimizer) = makePropertyTest (fromJust progToDistill) distilled
        let distillerIsCorrectTestCaseName = printf "%s: evaluation results of original and distilled programs are equal" fileToDistill 
        let distillerIsOptimizerTestCaseName = printf "%s: evaluation of the distilled program requires less resources than evaluation of the original one" fileToDistill 
        return $ testGroup 
                    fileToDistill 
                    [ testProperty distillerIsCorrectTestCaseName distillerIsCorrect,
                      testProperty distillerIsOptimizerTestCaseName distillerIsOptimizer]
  else do
    let testCaseName = printf "Parsing: %s" fileToDistill
    let assertion = assertFailure $ printf "program: %s; imports: %s." fileToDistill importsForDistill
    return $ testCase testCaseName assertion


test_plusMinus_2_property :: IO TestTree
test_plusMinus_2_property = do createTest "plusMinus_2" "inputs/" cases defaultTimeout 
    where
    cases origProg distilledProg = do (property p1, property p2)
        where 
        getEvaluationResults = do  
            n <- forAll genNat
            m <- forAll genNat            
            return $ getEvalResults [("n", natToTerm n), ("m", natToTerm m)] origProg distilledProg
        p1 = do
                ((origRes, _, _), (distilledRes, _,_)) <- getEvaluationResults                            
                origRes === distilledRes
        p2 = do  
                ((_, origReductions, origAllocations), (_, distilledReductions,distilledAllocations)) <- getEvaluationResults
                (origReductions >= distilledReductions && origAllocations >= distilledAllocations) === True
        

test_plusMinus_1_property :: IO TestTree
test_plusMinus_1_property = do createTest "plusMinus_1" "inputs/" cases defaultTimeout 
    where
    cases origProg distilledProg = do (property p1, property p2)
        where 
        getEvaluationResults = do  
            n <- forAll genNat
            m <- forAll genNat            
            return $ getEvalResults [("n", natToTerm n), ("m", natToTerm m)] origProg distilledProg
        p1 = do
                ((origRes, _, _), (distilledRes, _,_)) <- getEvaluationResults                            
                origRes === distilledRes
        p2 = do  
                ((_, origReductions, origAllocations), (_, distilledReductions,distilledAllocations)) <- getEvaluationResults
                (origReductions >= distilledReductions && origAllocations >= distilledAllocations) === True
    