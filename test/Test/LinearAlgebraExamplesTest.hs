{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

module Test.LinearAlgebraExamplesTest where

import qualified Test.Tasty.Hedgehog
import qualified Hedgehog.Gen as Gen
import Hedgehog ()
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.HUnit (testCase, (@?=), assertFailure)

import Test.Generators ()
import Test.TestHelpers (getEvalResults, load, loadFileToTerm)
import Term (Term)
import Trans (dist)
import Helpers ()

import Control.Monad ()
import Control.Exception ()
import Text.Printf (printf)
import Data.Maybe (fromJust, isJust)
import System.FilePath.Posix (takeBaseName)
import Data.Bifunctor (Bifunctor(second))

m512x512 :: [FilePath]
m512x512 =   
    [ 
      "inputs/data/dw256A_512x512_nnz_2480.pot",
      "inputs/data/dwb512_512x512_nnz_2500.pot",
      "inputs/data/dwt_503_512x512_nnz_3265.pot",
      "inputs/data/tomography_512x512_nnz_28726.pot",
      "inputs/data/Trefethen_500_512x512_nnz_4489.pot",
      "inputs/data/diag_512x512.pot"
    ]

m256x256 :: [FilePath]
m256x256 =  
    [ 
      "inputs/data/dwt_245_256x256_nnz_853.pot",
      "inputs/data/n3c5-b4_256x256_nnz_1260.pot",
      "inputs/data/Steam1_256x256_nnz_3762.pot",
      "inputs/data/can_256_256x256_nnz_1586.pot",
      "inputs/data/diag_256x256.pot"
    ]  

m128x128 :: [FilePath]
m128x128 = 
    [ 
      "inputs/data/football_128x128_nnz_613.pot",
      "inputs/data/GD98_b_128x128_nnz_207.pot",
      "inputs/data/gent113_128x128_nnz_655.pot",
      "inputs/data/Journals_128x128_nnz_6096.pot",
      "inputs/data/robot_128x128_nnz_870.pot",
      "inputs/data/diag_128x128.pot"
    ]  

m64x64 :: [FilePath]
m64x64 = 
    [ 
      "inputs/data/bfwa62_64x64_nnz_450.pot",
      "inputs/data/can_61_64x64_nnz_309.pot",
      "inputs/data/dolphins_64x64_nnz_159.pot",
      "inputs/data/GD99_b_64x64_nnz_127.pot",
      "inputs/data/will57_64x64_nnz_281.pot",
      "inputs/data/diag_64x64.pot"
    ]  

m2x2 :: [FilePath]
m2x2 =
    [
      "inputs/data/Small_1_2x2.pot",
      "inputs/data/Small_2_2x2.pot"
    ]

m4x4 :: [FilePath]
m4x4 =
    [
      "inputs/data/Small_1_4x4.pot",
      "inputs/data/Small_2_4x4.pot"
    ]

genCases :: 
  String -> Maybe (Term, [(String, ([String], Term))])
  -> String -> [[(String, FilePath)]] -> [TestTree]
genCases fileToDistill progToDistill logFileName =
   map $
    \bindingsInfo -> 
        testCase "tc" ( do
              _bindings <- 
                mapM 
                  (\(vName, filePath) -> do 
                      term <-  loadFileToTerm filePath
                      return ((vName, term),(vName, filePath))
                  ) bindingsInfo
              
              let bindings = 
                    foldl 
                      (\stt ((vName, term), info) -> 
                          case stt of
                            Right l -> 
                              case term of 
                                Left e -> Left e
                                Right x -> Right (((vName, x), info) : l)
                            Left e -> Left e
                      ) (Right []) _bindings

              case bindings of
                Left e -> assertFailure $ printf "Matrices can not be loaded: %s" (show e)
                Right _b -> do
                  let (b, bindingsInfo) = unzip _b
                  let ((origRes, origReductions, origAllocations), (distilledRes, distilledReductions, distilledAllocations)) = 
                        getEvalResults b (fromJust progToDistill) (dist $ fromJust progToDistill)
                      info = printf "%s; %s; %s; %s; %s; %s \n" 
                            (takeBaseName fileToDistill)
                            (show $ map (Data.Bifunctor.second takeBaseName) bindingsInfo) 
                            (show origReductions) 
                            (show origAllocations) 
                            (show distilledReductions) 
                            (show distilledAllocations)
                  appendFile logFileName info
                  putStr info
                  origReductions >= distilledReductions && origAllocations >= distilledAllocations && origRes == distilledRes @?= True )


createRealWorldTest :: String -> String -> [[(String, FilePath)]] -> IO TestTree
createRealWorldTest fileToDistill importsForDistill bindingsInfo = do
  let logFileName = takeBaseName fileToDistill ++ "_log.csv"
  appendFile logFileName "Test case; Bindings; Original reductions; Original allocations; Distilled reductions; Distilled allocations \n"  
  progToDistill <- load fileToDistill importsForDistill    
  return $ testGroup fileToDistill (
    if isJust progToDistill
    then genCases fileToDistill progToDistill logFileName bindingsInfo     
    else do
      let testCaseName = printf "Parsing: %s" fileToDistill
          assertion = assertFailure $ printf "program: %s; imports: %s." fileToDistill importsForDistill
      [testCase testCaseName assertion]
   )

test_matrices_add_add :: IO TestTree
test_matrices_add_add = createRealWorldTest "linearAlgebraExamples/addAdd" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64   , y <- m64x64   , z <- m64x64   ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m128x128 , y <- m128x128 , z <- m128x128 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m256x256 , y <- m256x256 , z <- m256x256 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m512x512 , y <- m512x512 , z <- m512x512 ]
      

test_matrices_add_add_add_1 :: IO TestTree
test_matrices_add_add_add_1 = createRealWorldTest "linearAlgebraExamples/addAddAdd1" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m64x64   , y <- m64x64   , z <- m64x64   , q <- m64x64   ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m128x128 , y <- m128x128 , z <- m128x128 , q <- m128x128 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m256x256 , y <- m256x256 , z <- m256x256 , q <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m512x512 , y <- m512x512 , z <- m512x512 , q <- m512x512 ]

test_matrices_add_add_add_2 :: IO TestTree
test_matrices_add_add_add_2 = createRealWorldTest "linearAlgebraExamples/addAddAdd2" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m64x64, y <- m64x64, z <- m64x64, q <- m64x64 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m128x128, y <- m128x128, z <- m128x128, q <- m128x128 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m256x256, y <- m256x256, z <- m256x256, q <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z), ("m4",q)] | x <- m512x512, y <- m512x512, z <- m512x512, q <- m512x512 ]

test_matrices_add_kron :: IO TestTree
test_matrices_add_kron = createRealWorldTest "linearAlgebraExamples/addKron2" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64, y <- m2x2, z <- m128x128 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m64x64, y <- m4x4, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m128x128, y <- m2x2, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m128x128, y <- m4x4, z <- m512x512 ] ++
        [ [("m1",x), ("m2",y) , ("m3",z)] | x <- m256x256, y <- m2x2, z <- m512x512 ]

test_matrices_add_kron3 :: IO TestTree
test_matrices_add_kron3 = createRealWorldTest "linearAlgebraExamples/addKron3" "inputs/" bindings
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

test_matrices_map_add :: IO TestTree
test_matrices_map_add = createRealWorldTest "linearAlgebraExamples/mapAdd" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y)] | x <- m64x64, y <- m64x64 ] ++
        [ [("m1",x), ("m2",y)] | x <- m128x128, y <- m128x128 ] ++
        [ [("m1",x), ("m2",y)] | x <- m256x256, y <- m256x256 ] ++
        [ [("m1",x), ("m2",y)] | x <- m512x512, y <- m512x512 ]

test_matrices_map_kron :: IO TestTree
test_matrices_map_kron = createRealWorldTest "linearAlgebraExamples/mapKron" "inputs/" bindings
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
        
test_matrices_kron_mask :: IO TestTree
test_matrices_kron_mask = createRealWorldTest "linearAlgebraExamples/kronMask" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m64x64,   y <- m2x2, z <- m128x128 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m64x64,   y <- m4x4, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m128x128, y <- m2x2, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m128x128, y <- m4x4, z <- m512x512 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m256x256, y <- m2x2, z <- m512x512 ]

test_matrices_add_mask :: IO TestTree
test_matrices_add_mask = createRealWorldTest "linearAlgebraExamples/addMask" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m64x64,   y <- m64x64,   z <- m64x64 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m128x128, y <- m128x128, z <- m128x128 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m256x256, y <- m256x256, z <- m256x256 ] ++
        [ [("m1",x), ("m2",y), ("m3",z)] | x <- m512x512, y <- m512x512, z <- m512x512 ]

test_matrices_add_kron5_constant_matrix :: IO TestTree
test_matrices_add_kron5_constant_matrix = createRealWorldTest "linearAlgebraExamples/addKron5_constant_matrix" "inputs/" bindings
    where
    bindings =           
        [ [("m1",x), ("m2",y)] | x <- m64x64, y <- m64x64 ] ++
        [ [("m1",x), ("m2",y)] | x <- m128x128, y <- m128x128 ] ++
        [ [("m1",x), ("m2",y)] | x <- m256x256, y <- m256x256 ] ++
        [ [("m1",x), ("m2",y)] | x <- m512x512, y <- m512x512 ]
