{-# LANGUAGE InstanceSigs #-}

module Test.LinearAlgebraExamplesTest where

import Control.Monad

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


createRealWorldTest :: 
  (Foldable t, Show (t (String, FilePath))) =>
  String -> String -> [t (String, FilePath)] -> IO TestTree
createRealWorldTest fileToDistill importsForDistill bindingsInfo =  do  
  let loadedBindings = 
        map (foldM (\stt (vName, file) -> 
              fmap (\r -> 
                case stt of
                  Right l ->  
                    case r of 
                      Left e -> Left e
                      Right x -> Right (((vName,x),(vName,file)) : l)
                  Left e -> Left e ) (loadFileToTerm file)) 
                  (Right []))
              bindingsInfo                             
  progToDistill <- load fileToDistill importsForDistill  
  if isJust progToDistill
  then do
    distillationResult <- try (evaluate $ dist (fromJust progToDistill)) :: IO (Either SomeException (Term, [(String, ([String], Term))]))
    let testCaseName = printf "Distillation of %s" fileToDistill
    case distillationResult of
      Left ex -> do
        let assertion = assertFailure $ printf "program: %s; imports: %s; exception: %s" fileToDistill importsForDistill (show ex)        
        return $ testCase testCaseName assertion
      Right distilled -> do
        cases <-
              mapM (\lB -> do
                        bindings <- lB
                        case bindings of
                          Left e -> do
                            let assertion = assertFailure $ printf "program: %s; imports: %s; exception: %s" fileToDistill importsForDistill (show e)
                            return $ testCase testCaseName assertion
                          Right _bindings -> do
                            let (bindings, bindingsInfo) = unzip _bindings
                            let ((origRes, origReductions, origAllocations), (distilledRes, distilledReductions, distilledAllocations)) = getEvalResults bindings (fromJust progToDistill) distilled
                                assertion = origRes @?= distilledRes
                                testCaseName = printf "Evaluation of %s. Computed for %s. Original reductions %s, allocations %s. Distilled reductions %s, allocations %s." 
                                                      fileToDistill 
                                                      (show bindingsInfo)
                                                      (show origReductions)
                                                      (show origAllocations)
                                                      (show distilledReductions)
                                                      (show distilledAllocations)
                            return $ testCase testCaseName assertion) loadedBindings
        return $ testGroup fileToDistill cases
  else do
    let testCaseName = printf "Parsing: %s" fileToDistill
    let assertion = assertFailure $ printf "program: %s; imports: %s." fileToDistill importsForDistill
    return $ testCase testCaseName assertion


--test_matrices_add_add_football_football_64x64 = do createRealWorldTest "linearAlgebraExamples/addAdd" "inputs/" getEvaluationResults
--    where
--    getEvaluationResults origProg distilledProg = do          
--        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
--        case m of 
--          Left e -> return $ Left e            
--          Right u -> 
--            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("m3", u)] origProg distilledProg
--
--test_matrices_add_add_add_1_football_football_64x64 = do createRealWorldTest "linearAlgebraExamples/addAddAdd1" "inputs/" getEvaluationResults
--    where
--    getEvaluationResults origProg distilledProg = do          
--        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
--        case m of 
--          Left e -> return $ Left e            
--          Right u -> 
--            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("m3", u), ("m4", u)] origProg distilledProg
--
--test_matrices_add_add_add_2_football_football_64x64 = do createRealWorldTest "linearAlgebraExamples/addAddAdd2" "inputs/" getEvaluationResults
--    where
--    getEvaluationResults origProg distilledProg = do          
--        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
--        case m of 
--          Left e -> return $ Left e            
--          Right u -> 
--            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("m3", u), ("m4", u)] origProg distilledProg
--
--
--test_matrices_add_kron_football_64x64_small_2x2 = do createRealWorldTest "linearAlgebraExamples/addKron2" "inputs/" getEvaluationResults
--    where
--    getEvaluationResults origProg distilledProg = do          
--        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
--        n <- loadFileToTerm "inputs/data/Small_1_2x2.pot"
--        case (m,n) of 
--          (Left e,x) -> return $ Left e            
--          (x, Left e) -> return $ Left e            
--          (Right u, Right v) -> 
--            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("m3", v)] origProg distilledProg

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


--test_matrices_map_add_football_football_64x64 = do createRealWorldTest "linearAlgebraExamples/mapAdd" "inputs/" getEvaluationResults
--    where
--    getEvaluationResults origProg distilledProg = do          
--        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
--        case m of 
--          Left e -> return $ Left e            
--          Right u -> 
--            return $ Right $ getEvalResults [("m1", u), ("m2", u)] origProg distilledProg

test_matrices_map_kron_football_64x64_small_1_2x2 = do createRealWorldTest "linearAlgebraExamples/mapKron" "inputs/" bindings
    where
    bindings = 
      [
        [("m1","inputs/data/bfwa62_64x64_nnz_450.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/can_61_64x64_nnz_309.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/dolphins_64x64_nnz_159.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/GD99_b_64x64_nnz_127.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/will57_64x64_nnz_281.pot"),("m2", "inputs/data/Small_1_2x2.pot")],

        [("m1","inputs/data/football_128x128_nnz_613.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/GD98_b_128x128_nnz_207.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/gent113_128x128_nnz_655.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/Journals_128x128_nnz_6096.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/robot_128x128_nnz_870.pot"),("m2", "inputs/data/Small_1_2x2.pot")],

        [("m1","inputs/data/dwt_245_256x256_nnz_853.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/n3c5-b4_256x256_nnz_1260.pot"),("m2", "inputs/data/Small_1_2x2.pot")], 
        [("m1","inputs/data/Steam1_256x256_nnz_3762.pot"),("m2", "inputs/data/Small_1_2x2.pot")],        
        [("m1","inputs/data/can_256_256x256_nnz_1586.pot"),("m2", "inputs/data/Small_1_2x2.pot")], 
        
        [("m1","inputs/data/dw256A_512x512_nnz_2480.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/dwb512_512x512_nnz_2500.pot"),("m2", "inputs/data/Small_1_2x2.pot")], 
        [("m1","inputs/data/dwt_503_512x512_nnz_3265.pot"),("m2", "inputs/data/Small_1_2x2.pot")],        
        [("m1","inputs/data/tomography_512x512_nnz_28726.pot"),("m2", "inputs/data/Small_1_2x2.pot")],
        [("m1","inputs/data/Trefethen_500_512x512_nnz_4489.pot"),("m2", "inputs/data/Small_1_2x2.pot")]
      ]

--test_matrices_kron_mask_football_64x64_small_1_2x2_mask1 = do createRealWorldTest "linearAlgebraExamples/kronMask" "inputs/" getEvaluationResults
--    where
--    getEvaluationResults origProg distilledProg = do          
--        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
--        n <- loadFileToTerm "inputs/data/Small_1_2x2.pot"
--        msk <- loadFileToTerm "inputs/data/Mask1.pot"
--        case (m,n,msk) of 
--          (Left e,x,y) -> return $ Left e
--          (x, Left e,y) -> return $ Left e
--          (x, y, Left e) -> return $ Left e
--          (Right u, Right v, Right msk) -> 
--            return $ Right $ getEvalResults [("m1", u), ("m2", v), ("msk", msk)] origProg distilledProg
--
--test_matrices_kron_mask_football_64x64_small_1_2x2_mask2 = do createRealWorldTest "linearAlgebraExamples/kronMask" "inputs/" getEvaluationResults
--    where
--    getEvaluationResults origProg distilledProg = do          
--        m <- loadFileToTerm "inputs/data/Football_64x64.pot"
--        n <- loadFileToTerm "inputs/data/Small_1_2x2.pot"
--        msk <- loadFileToTerm "inputs/data/Mask2.pot"
--        case (m,n,msk) of 
--          (Left e,x,y) -> return $ Left e
--          (x, Left e,y) -> return $ Left e
--          (x, y, Left e) -> return $ Left e
--          (Right u, Right v, Right msk) -> 
--            return $ Right $ getEvalResults [("m1", u), ("m2", v), ("msk", msk)] origProg distilledProg
--
--
--test_matrices_add_mask_football_football_64x64_mask1 = do createRealWorldTest "linearAlgebraExamples/addMask" "inputs/" getEvaluationResults
--    where
--    getEvaluationResults origProg distilledProg = do          
--        m <- loadFileToTerm "inputs/data/Football_64x64.pot"        
--        msk <- loadFileToTerm "inputs/data/Mask1.pot"
--        case (m,msk) of 
--          (Left e,x) -> return $ Left e
--          (x, Left e) -> return $ Left e          
--          (Right u, Right msk) -> 
--            return $ Right $ getEvalResults [("m1", u), ("m2", u), ("msk", msk)] origProg distilledProg
--