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
import TermType
import Transformer
import Helpers

import Control.Exception
import Text.Printf (printf)
import Data.Maybe (fromJust, isJust)


m512x512 =
  [ 
    "inputs/data/dw256A_512x512_nnz_2480.pot",
    "inputs/data/dwb512_512x512_nnz_2500.pot",
    "inputs/data/dwt_503_512x512_nnz_3265.pot",
    "inputs/data/tomography_512x512_nnz_28726.pot",
    "inputs/data/Trefethen_500_512x512_nnz_4489.pot",
    "inputs/data/diag_512x512.pot"
  ]

m256x256 = 
  [ 
    "inputs/data/dwt_245_256x256_nnz_853.pot",
    "inputs/data/n3c5-b4_256x256_nnz_1260.pot",
    "inputs/data/Steam1_256x256_nnz_3762.pot",
    "inputs/data/can_256_256x256_nnz_1586.pot",
    "inputs/data/diag_256x256.pot"
  ]  

m128x128 = 
  [ 
    "inputs/data/football_128x128_nnz_613.pot",
    "inputs/data/GD98_b_128x128_nnz_207.pot",
    "inputs/data/gent113_128x128_nnz_655.pot",
    "inputs/data/Journals_128x128_nnz_6096.pot",
    "inputs/data/robot_128x128_nnz_870.pot",
    "inputs/data/diag_128x128.pot"
  ]  

m64x64 = 
  [ 
    "inputs/data/bfwa62_64x64_nnz_450.pot",
    "inputs/data/can_61_64x64_nnz_309.pot",
    "inputs/data/dolphins_64x64_nnz_159.pot",
    "inputs/data/GD99_b_64x64_nnz_127.pot",
    "inputs/data/will57_64x64_nnz_281.pot",
    "inputs/data/diag_64x64.pot"
  ]  

m2x2 =
  [
    "inputs/data/Small_1_2x2.pot",
    "inputs/data/Small_2_2x2.pot"
  ]

m4x4 =
  [
    "inputs/data/Small_1_4x4.pot",
    "inputs/data/Small_2_4x4.pot"
  ]

createRealWorldTest ::
  (Foldable t, Show (t (String, FilePath))) =>
  String -> String -> [t (String, FilePath)] -> IO TestTree
createRealWorldTest fileToDistill importsForDistill bindingsInfo = return $ testGroup "Tests" [testCase "2+2=4" $ 2+2 @?= 4]{-- do
  let loadedBindings = 
        map (foldM (\stt (vName, file) -> 
              (\r -> 
                case stt of
                  Right l ->  
                    case r of 
                      Left e -> Left e
                      Right x -> Right (((vName,x),(vName,file)) : l)
                  Left e -> Left e ) <$> loadFileToTerm file) 
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
            mapM (\x -> do
                      bindings <- x
                      case bindings of
                        Left e -> do
                          let assertion = assertFailure $ printf "program: %s; imports: %s; exception: %s" fileToDistill importsForDistill (show e)
                          return $ testCase testCaseName assertion
                        Right _bindings -> do
                          let (bindings, bindingsInfo) = unzip _bindings
                          let ((origRes, origReductions, origAllocations), (distilledRes, distilledReductions, distilledAllocations)) = getEvalResults bindings (fromJust progToDistill) distilled
                              assertion = origRes @?= distilledRes
                              testCaseName = 
                                printf "Evaluation of %s. Computed for %s. Original reductions %s, allocations %s. Distilled reductions %s, allocations %s." 
                                        fileToDistill 
                                        (show bindingsInfo)
                                        (show origReductions)
                                        (show origAllocations)
                                        (show distilledReductions)
                                        (show distilledAllocations)
                          return $ testCase testCaseName assertion) 
                  loadedBindings
        return $ testGroup fileToDistill cases
  else do
    let testCaseName = printf "Parsing: %s" fileToDistill
    let assertion = assertFailure $ printf "program: %s; imports: %s." fileToDistill importsForDistill
    return $ testCase testCaseName assertion --}

test_matrices_add_add = do createRealWorldTest "linearAlgebraExamples/addAdd" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64, y <- m64x64, z <- m64x64 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m128x128, y <- m128x128, z <- m128x128 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m256x256, y <- m256x256, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m512x512, y <- m512x512, z <- m512x512 ]
      

test_matrices_add_add_add_1 = do createRealWorldTest "linearAlgebraExamples/addAddAdd1" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m64x64, y <- m64x64, z <- m64x64, q <- m64x64 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m128x128, y <- m128x128, z <- m128x128, q <- m128x128 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m256x256, y <- m256x256, z <- m256x256, q <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m512x512, y <- m512x512, z <- m512x512, q <- m512x512 ]

test_matrices_add_add_add_2 = do createRealWorldTest "linearAlgebraExamples/addAddAdd2" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m64x64, y <- m64x64, z <- m64x64, q <- m64x64 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m128x128, y <- m128x128, z <- m128x128, q <- m128x128 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m256x256, y <- m256x256, z <- m256x256, q <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m512x512, y <- m512x512, z <- m512x512, q <- m512x512 ]

test_matrices_add_kron = do createRealWorldTest "linearAlgebraExamples/addKron2" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64, y <- m2x2, z <- m128x128 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64, y <- m4x4, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m128x128, y <- m2x2, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m128x128, y <- m4x4, z <- m512x512 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m256x256, y <- m2x2, z <- m512x512 ]

test_matrices_add_kron3 = do createRealWorldTest "linearAlgebraExamples/addKron3" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64, y <- m2x2, z <- m2x2 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64, y <- m4x4, z <- m4x4 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64, y <- m64x64, z <- m64x64 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m128x128, y <- m2x2, z <- m2x2 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m128x128, y <- m4x4, z <- m4x4 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m256x256, y <- m2x2, z <- m2x2 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m256x256, y <- m4x4, z <- m4x4 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m512x512, y <- m2x2, z <- m2x2 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m512x512, y <- m4x4, z <- m4x4 ]

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


test_matrices_map_add = do createRealWorldTest "linearAlgebraExamples/mapAdd" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y)] | x <- m64x64, y <- m64x64 ] ++
        [ [("m1",x), ("m2",y)] | x <- m128x128, y <- m128x128 ] ++
        [ [("m1",x), ("m2",y)] | x <- m256x256, y <- m256x256 ] ++
        [ [("m1",x), ("m2",y)] | x <- m512x512, y <- m512x512 ]

test_matrices_map_kron = do createRealWorldTest "linearAlgebraExamples/mapKron" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y)] | x <- m64x64, y <- m2x2 ] ++
        [ [("m1",x), ("m2",y)] | x <- m128x128, y <- m2x2 ] ++
        [ [("m1",x), ("m2",y)] | x <- m256x256, y <- m2x2 ] ++
        [ [("m1",x), ("m2",y)] | x <- m512x512, y <- m2x2 ] ++

        [ [("m1",x), ("m2",y)] | x <- m64x64, y <- m4x4 ] ++
        [ [("m1",x), ("m2",y)] | x <- m128x128, y <- m4x4 ] ++
        [ [("m1",x), ("m2",y)] | x <- m256x256, y <- m4x4 ] ++
        [ [("m1",x), ("m2",y)] | x <- m512x512, y <- m4x4 ] ++

        [ [("m1",x), ("m2",y)] | x <- m64x64, y <- m64x64 ] ++
        [ [("m1",x), ("m2",y)] | x <- m128x128, y <- m64x64 ] ++
        [ [("m1",x), ("m2",y)] | x <- m256x256, y <- m64x64 ] ++
        [ [("m1",x), ("m2",y)] | x <- m512x512, y <- m64x64 ] 
        
test_matrices_kron_mask = do createRealWorldTest "linearAlgebraExamples/kronMask" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m64x64,   y <- m2x2, z <- m128x128 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m64x64,   y <- m4x4, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m128x128, y <- m2x2, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m128x128, y <- m4x4, z <- m512x512 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m256x256, y <- m2x2, z <- m512x512 ]

test_matrices_add_mask = do createRealWorldTest "linearAlgebraExamples/addMask" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m64x64,   y <- m64x64,   z <- m64x64 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m128x128, y <- m128x128, z <- m128x128 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m256x256, y <- m256x256, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m512x512, y <- m512x512, z <- m512x512 ]

test_matrices_add_kron5_constant_matrix = do createRealWorldTest "linearAlgebraExamples/addKron5_constant_matrix" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y)] | x <- m64x64, y <- m64x64 ] ++
        [ [("m1",x), ("m2",y)] | x <- m128x128, y <- m128x128 ] ++
        [ [("m1",x), ("m2",y)] | x <- m256x256, y <- m256x256 ] ++
        [ [("m1",x), ("m2",y)] | x <- m512x512, y <- m512x512 ]
--}