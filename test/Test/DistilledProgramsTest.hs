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
