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

createTest :: (Ord b, Ord c, Eq a, Show a) =>
                String
                -> String
                -> ((Term, [(String, ([String], Term))])
                    -> (Term, [(String, ([String], Term))])
                    -> PropertyT IO ((a, b, c), (a, b, c)))
                -> p
                -> IO TestTree
createTest fileToDistill importsForDistill getEvaluationResults timeoutForDistillation =  do
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

        let (distillerIsCorrect, distillerIsOptimizer) =
                let p1 = do ((origRes, _, _), (distilledRes, _, _)) <- getEvaluationResults (fromJust progToDistill) distilled                           
                            origRes === distilledRes 
                    p2 = do ((_, origReductions, origAllocations), (_, distilledReductions,distilledAllocations)) <- getEvaluationResults (fromJust progToDistill) distilled
                            (origReductions >= distilledReductions && origAllocations >= distilledAllocations) === True 
                in 
                (property p1, property p2)
            
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


--test_plusMinus_2_property :: IO TestTree
--test_plusMinus_2_property = do createTest "plusMinus_2" "inputs/" getEvaluationResults defaultTimeout 
--    where 
--    getEvaluationResults origProg distilledProg = do  
--        n <- forAll genNat
--        m <- forAll genNat            
--        return $ getEvalResults [("n", natToTerm n), ("m", natToTerm m)] origProg distilledProg
--            
--
--test_plusMinus_1_property :: IO TestTree
--test_plusMinus_1_property = do createTest "plusMinus_1" "inputs/" getEvaluationResults defaultTimeout 
--    where
--    getEvaluationResults origProg distilledProg = do  
--        n <- forAll genNat
--        m <- forAll genNat            
--        return $ getEvalResults [("n", natToTerm n), ("m", natToTerm m)] origProg distilledProg