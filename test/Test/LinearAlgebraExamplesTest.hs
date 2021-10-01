{-# LANGUAGE InstanceSigs #-}

module Test.LinearAlgebraExamplesTest where

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

createRealWorldTest fileToDistill importsForDistill getEvaluationResults =  do
  progToDistill <- load fileToDistill importsForDistill  
  if isJust progToDistill
  then do
    distillationResult <- try (evaluate $ dist (fromJust progToDistill)) :: IO (Either SomeException (Term, [(String, ([String], Term))]))
    let testCaseName = printf "Distillation of %s" fileToDistill
    case distillationResult of
      Left ex -> do
        let assertion = assertFailure $ printf "program: %s; imports: %s; exception: %s" fileToDistill importsForDistill (show ex)        
        return $ testCase testCaseName assertion
      Right  distilled -> do        
        p <- getEvaluationResults (fromJust progToDistill) distilled                                   
        case p of 
          Left ex -> do
            let assertion = assertFailure $ printf "program: %s; imports: %s; exception: %s" fileToDistill importsForDistill (show ex)
            return $ testCase testCaseName assertion
          Right ((origRes, origReductions, origAllocations), (distilledRes, distilledReductions, distilledAllocations)) -> do
            let assertion = origRes @?= distilledRes
                testCaseName = printf "Distillation of %s. Original reductions %s, allocations %s. Distilled reductions %s, allocations %s." 
                                      fileToDistill 
                                      (show origReductions)
                                      (show origAllocations)
                                      (show distilledReductions)
                                      (show distilledAllocations)
            return $ testCase testCaseName assertion
  else do
    let testCaseName = printf "Parsing: %s" fileToDistill
    let assertion = assertFailure $ printf "program: %s; imports: %s." fileToDistill importsForDistill
    return $ testCase testCaseName assertion


test_matrices_add_add_football_football_64x64 = do createRealWorldTest "linearAlgebraExamples/addAdd" "inputs/" getEvaluationResults
    where
    getEvaluationResults origProg distilledProg = do          
        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
        case m of 
          Left e -> return $ Left e            
          Right u -> 
            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("m3", u)] origProg distilledProg

test_matrices_add_add_add_1_football_football_64x64 = do createRealWorldTest "linearAlgebraExamples/addAddAdd1" "inputs/" getEvaluationResults
    where
    getEvaluationResults origProg distilledProg = do          
        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
        case m of 
          Left e -> return $ Left e            
          Right u -> 
            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("m3", u), ("m4", u)] origProg distilledProg

test_matrices_add_add_add_2_football_football_64x64 = do createRealWorldTest "linearAlgebraExamples/addAddAdd2" "inputs/" getEvaluationResults
    where
    getEvaluationResults origProg distilledProg = do          
        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
        case m of 
          Left e -> return $ Left e            
          Right u -> 
            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("m3", u), ("m4", u)] origProg distilledProg


test_matrices_add_kron_football_64x64_small_2x2 = do createRealWorldTest "linearAlgebraExamples/addKron2" "inputs/" getEvaluationResults
    where
    getEvaluationResults origProg distilledProg = do          
        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
        n <- loadFileToTerm "inputs/data/Small_1_2x2.pot"
        case (m,n) of 
          (Left e,x) -> return $ Left e            
          (x, Left e) -> return $ Left e            
          (Right u, Right v) -> 
            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("m3", v)] origProg distilledProg

--test_matrices_add_kron_kron_football_64x64_small_2x2 = do test <- createRealWorldTest "linearAlgebraExamples/addKron1" "inputs/" getEvaluationResults
--                                                          return $ ignoreTest test    
--    where
--    getEvaluationResults origProg distilledProg = do          
--        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
--        n <- loadFileToTerm "inputs/data/Small_1_2x2.pot"
--        case (m,n) of 
--          (Left e,x) -> return $ Left e            
--          (x, Left e) -> return $ Left e            
--          (Right u, Right v) -> 
--            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("m3", v), ("m4", v)] origProg distilledProg


test_matrices_map_add_football_football_64x64 = do createRealWorldTest "linearAlgebraExamples/mapAdd" "inputs/" getEvaluationResults
    where
    getEvaluationResults origProg distilledProg = do          
        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
        case m of 
          Left e -> return $ Left e            
          Right u -> 
            return $ Right $ getEvalResults [("m1", u), ("m2", u)] origProg distilledProg

test_matrices_map_kron_football_64x64_small_1_2x2 = do createRealWorldTest "linearAlgebraExamples/mapKron" "inputs/" getEvaluationResults
    where
    getEvaluationResults origProg distilledProg = do          
        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
        n <- loadFileToTerm "inputs/data/Small_1_2x2.pot"
        case (m,n) of 
          (Left e,x) -> return $ Left e            
          (x, Left e) -> return $ Left e            
          (Right u, Right v) -> 
            return $ Right $ getEvalResults [("m1", u), ("m2", v)] origProg distilledProg

test_matrices_kron_mask_football_64x64_small_1_2x2_mask1 = do createRealWorldTest "linearAlgebraExamples/kronMask" "inputs/" getEvaluationResults
    where
    getEvaluationResults origProg distilledProg = do          
        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
        n <- loadFileToTerm "inputs/data/Small_1_2x2.pot"
        msk <- loadFileToTerm "inputs/data/Mask1.pot"
        case (m,n,msk) of 
          (Left e,x,y) -> return $ Left e
          (x, Left e,y) -> return $ Left e
          (x, y, Left e) -> return $ Left e
          (Right u, Right v, Right msk) -> 
            return $ Right $ getEvalResults [("m1", u), ("m2", v), ("msk", msk)] origProg distilledProg

test_matrices_kron_mask_football_64x64_small_1_2x2_mask2 = do createRealWorldTest "linearAlgebraExamples/kronMask" "inputs/" getEvaluationResults
    where
    getEvaluationResults origProg distilledProg = do          
        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
        n <- loadFileToTerm "inputs/data/Small_1_2x2.pot"
        msk <- loadFileToTerm "inputs/data/Mask2.pot"
        case (m,n,msk) of 
          (Left e,x,y) -> return $ Left e
          (x, Left e,y) -> return $ Left e
          (x, y, Left e) -> return $ Left e
          (Right u, Right v, Right msk) -> 
            return $ Right $ getEvalResults [("m1", u), ("m2", v), ("msk", msk)] origProg distilledProg


test_matrices_add_mask_football_football_64x64_mask1 = do createRealWorldTest "linearAlgebraExamples/addMask" "inputs/" getEvaluationResults
    where
    getEvaluationResults origProg distilledProg = do          
        m <- loadFileToTerm "inputs/data/Football_64x64.pot"        
        msk <- loadFileToTerm "inputs/data/Mask1.pot"
        case (m,msk) of 
          (Left e,x) -> return $ Left e
          (x, Left e) -> return $ Left e          
          (Right u, Right msk) -> 
            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("msk", msk)] origProg distilledProg
