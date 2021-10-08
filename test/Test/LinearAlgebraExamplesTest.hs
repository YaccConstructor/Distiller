{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

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

genCases :: 
  Maybe (Term, [(String, ([String], Term))])
  -> [[(String, FilePath)]] -> [TestTree]
genCases progToDistill =
  map 
    (\bindingsInfo -> 
        testCase "tc" ( do
              _bindings <- 
                mapM 
                  (\(vName, filePath) -> do 
                      term <-  loadFileToTerm filePath
                      return (vName, term)
                  ) bindingsInfo
              
              let bindings = 
                    foldl 
                      (\stt (vName, term) -> 
                          case stt of
                            Right l -> 
                              case term of 
                                Left e -> Left e
                                Right x -> Right ((vName,x) : l)
                            Left e -> Left e
                      ) (Right []) _bindings

              case bindings of
                Left e -> assertFailure $ printf "Matrices can not be loaded"
                Right b -> do
                  let ((origRes, origReductions, origAllocations), (distilledRes, distilledReductions, distilledAllocations)) = 
                        getEvalResults b (fromJust progToDistill) (dist $ fromJust progToDistill)
                  putStr $ printf "%s %s %s %s " (show origReductions) (show origAllocations) (show distilledReductions) (show distilledAllocations)
                  origRes @?= distilledRes)
    )  


createRealWorldTest :: String -> String -> [[(String, FilePath)]] -> IO TestTree
createRealWorldTest fileToDistill importsForDistill bindingsInfo = do
  progToDistill <- load fileToDistill importsForDistill    
  return $ testGroup fileToDistill (
    if isJust progToDistill
    then genCases progToDistill bindingsInfo          
    else do
      let testCaseName = printf "Parsing: %s" fileToDistill
          assertion = assertFailure $ printf "program: %s; imports: %s." fileToDistill importsForDistill
      [testCase testCaseName assertion]
   )

test_matrices_add_add = createRealWorldTest "linearAlgebraExamples/addAdd" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64   , y <- m64x64   , z <- m64x64   ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m128x128 , y <- m128x128 , z <- m128x128 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m256x256 , y <- m256x256 , z <- m256x256 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m512x512 , y <- m512x512 , z <- m512x512 ]
      

test_matrices_add_add_add_1 = createRealWorldTest "linearAlgebraExamples/addAddAdd1" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m64x64   , y <- m64x64   , z <- m64x64   , q <- m64x64   ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m128x128 , y <- m128x128 , z <- m128x128 , q <- m128x128 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m256x256 , y <- m256x256 , z <- m256x256 , q <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m512x512 , y <- m512x512 , z <- m512x512 , q <- m512x512 ]

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
        [ [("m1",x), ("m2",y)] | x <- m512x512, y <- m4x4 ]
        
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
