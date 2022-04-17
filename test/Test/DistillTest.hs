module Test.DistillTest where

import ExecutionHelpers
import Test.Tasty
import Test.Tasty.HUnit
import TermType
import Transformer
import Data.List
import Data.Maybe (fromJust, isJust)
import Text.Printf ( printf )
import Control.Exception
import Test.TestHelpers
import Distiller (distillProg)


createDistillationTest :: String -> String -> String -> String -> Integer -> IO TestTree
createDistillationTest fileToDistill importsForDistill fileWithGold importsForGold timeoutForDistillation = do
  progToDistill <- load fileToDistill importsForDistill
  (mainOfExpectedProg, y) <- fromJust <$> load fileWithGold importsForGold -- parsing golden file should always succeed
  let testCaseName = printf "Distillation of %s" fileToDistill
  if isJust progToDistill
  then do
    distillationResult <- try (evaluate $ distillProg (fromJust progToDistill)) :: IO (Either SomeException (Term, [(String, ([String], Term))]))
    case distillationResult of
      Left ex -> do 
        let assertion = assertFailure $ printf "program: %s; imports: %s; exception: %s" fileToDistill importsForDistill (show ex)
        return $ testCase testCaseName assertion
      Right  (mainOfDistilledProg, x) -> do
        let actual = ("main", ([], mainOfDistilledProg)) : x
        let expected = ("main", ([], mainOfExpectedProg)) : y
        let assertion = expected `intersect` actual @?= expected        
        return $ timeOutTest timeoutForDistillation testCaseName assertion
  else do
    let testCaseName = printf "Parsing: %s" fileToDistill
    let assertion = assertFailure $ printf "program: %s; imports: %s." fileToDistill importsForDistill
    return $ testCase testCaseName assertion

-- Basic tests

test_distillerBasicTest1 :: IO TestTree
test_distillerBasicTest1 = 
  createDistillationTest "plusassoc" "inputs/" "gold/plusassoc_gold" "inputs/" defaultTimeout

test_distillerBasicTest2 :: IO TestTree
test_distillerBasicTest2 = 
  createDistillationTest "appapp" "inputs/" "gold/appapp_gold" "inputs/" defaultTimeout

test_distillerBasicTest3 :: IO TestTree
test_distillerBasicTest3 = 
  createDistillationTest "map" "inputs/" "gold/map_gold" "inputs/" defaultTimeout

test_distillerBasicTest4 :: IO TestTree
test_distillerBasicTest4 = 
  createDistillationTest "pluscomm" "inputs/" "gold/pluscomm_gold" "inputs/" defaultTimeout

test_distillerBasicTest5 :: IO TestTree
test_distillerBasicTest5 = 
  createDistillationTest "revrev" "inputs/" "gold/revrev_gold" "inputs/" defaultTimeout

test_distillerBasicTest6 :: IO TestTree
test_distillerBasicTest6 = 
  createDistillationTest "mapmap" "inputs/" "gold/mapmap_gold" "inputs/" defaultTimeout

test_distillerBasicTest7 :: IO TestTree
test_distillerBasicTest7 = 
  createDistillationTest "mapfold" "inputs/" "gold/mapfold_gold" "inputs/" defaultTimeout    

test_distillerBasicTest8 :: IO TestTree
test_distillerBasicTest8 = 
  createDistillationTest "nonterm" "inputs/" "gold/nonterm_gold" "inputs/" defaultTimeout    

test_distillerBasicTest9 :: IO TestTree
test_distillerBasicTest9 = 
  createDistillationTest "palindrome" "inputs/" "gold/palindrome_gold" "inputs/" _10sec    

test_distillerBasicTest10 :: IO TestTree
test_distillerBasicTest10 = 
  createDistillationTest "sumfac" "inputs/" "gold/sumfac_gold" "inputs/" _10sec    

test_distillerBasicTest11 :: IO TestTree
test_distillerBasicTest11 = 
  createDistillationTest "neil1" "inputs/" "gold/neil1_gold" "inputs/" defaultTimeout    

test_distillerBasicTest12 :: IO TestTree
test_distillerBasicTest12 = 
  createDistillationTest "neil2" "inputs/" "gold/neil2_gold" "inputs/" defaultTimeout    

test_distillerBasicTest13 :: IO TestTree
test_distillerBasicTest13 = 
  createDistillationTest "neil3" "inputs/" "gold/neil3_gold" "inputs/" _10sec    

test_distillerBasicTest14 :: IO TestTree
test_distillerBasicTest14 = 
  createDistillationTest "plusMinus_1" "inputs/" "gold/plusMinus_1_gold" "inputs/" defaultTimeout    

test_distillerBasicTest15 :: IO TestTree
test_distillerBasicTest15 = 
  createDistillationTest "plusMinus_2" "inputs/" "gold/plusMinus_2_gold" "inputs/" defaultTimeout    

test_distillerBasicTest16 :: IO TestTree
test_distillerBasicTest16 = 
  createDistillationTest "multDiv_1" "inputs/" "gold/multDiv_1_gold" "inputs/" _10sec    

test_distillerBasicTest17 :: IO TestTree
test_distillerBasicTest17 = 
  createDistillationTest "multDiv_2" "inputs/" "gold/multDiv_2_gold" "inputs/" _10sec    

test_distillerBasicTest18 :: IO TestTree
test_distillerBasicTest18 = 
  createDistillationTest "plusMultDistrib" "inputs/" "gold/plusMultDistrib_gold" "inputs/" _10sec    

test_distillerBasicTest19 :: IO TestTree
test_distillerBasicTest19 = 
  createDistillationTest "natEq" "inputs/" "gold/natEq_gold" "inputs/" defaultTimeout    

test_distillerBasicTest20 :: IO TestTree
test_distillerBasicTest20 = 
   createDistillationTest "minus" "inputs/" "gold/minus_gold" "inputs/" defaultTimeout

test_distillerBasicTest21 :: IO TestTree
test_distillerBasicTest21 = 
    createDistillationTest "append_Zero" "inputs/" "gold/append_Zero_gold" "inputs/" defaultTimeout

test_distillerBasicTest22 :: IO TestTree
test_distillerBasicTest22 = 
    createDistillationTest "append" "inputs/" "gold/append_gold" "inputs/" defaultTimeout       

test_distillerBasicTest23 :: IO TestTree
test_distillerBasicTest23 = 
    createDistillationTest "and" "inputs/" "gold/and_gold" "inputs/" defaultTimeout

test_distillerBasicTest24 :: IO TestTree
test_distillerBasicTest24 = 
    createDistillationTest "or" "inputs/" "gold/or_gold" "inputs/" defaultTimeout
    
test_distillerBasicTest25 :: IO TestTree
test_distillerBasicTest25 =
    createDistillationTest "not" "inputs/" "gold/not_gold" "inputs/" defaultTimeout

test_distillerBasicTest26 :: IO TestTree
test_distillerBasicTest26 =
    createDistillationTest "and" "inputs/" "gold/and_gold" "inputs/" defaultTimeout

test_distillerBasicTest27 :: IO TestTree
test_distillerBasicTest27 =
    createDistillationTest "qrev" "inputs/" "gold/qrev_gold" "inputs/" defaultTimeout
-- Linear algebra tests

test_distillerLinearAlgebraTest1 :: IO TestTree
test_distillerLinearAlgebraTest1 = 
  createDistillationTest "linearAlgebraTests/addadd" "inputs/" "gold/linearAlgebra/addadd_gold" "inputs/" _10sec

test_distillerLinearAlgebraTest2 :: IO TestTree
test_distillerLinearAlgebraTest2 = 
  createDistillationTest "linearAlgebraTests/addmask" "inputs/" "gold/linearAlgebra/addmask_gold" "inputs/" _10sec

test_distillerLinearAlgebraTest3 :: IO TestTree
test_distillerLinearAlgebraTest3 = 
  createDistillationTest "linearAlgebraTests/multmask" "inputs/" "gold/linearAlgebra/multmask_gold" "inputs/" _10sec

test_distillerLinearAlgebraTest4 :: IO TestTree
test_distillerLinearAlgebraTest4 = 
  createDistillationTest "linearAlgebraTests/kronmask" "inputs/" "gold/linearAlgebra/kronmask_gold" "inputs/" _10sec

test_distillerLinearAlgebraTest5 :: IO TestTree
test_distillerLinearAlgebraTest5 = 
  createDistillationTest "linearAlgebraTests/reduceMask1" "inputs/" "gold/linearAlgebra/reduceMask1_gold" "inputs/" defaultTimeout

test_distillerLinearAlgebraTest6 :: IO TestTree
test_distillerLinearAlgebraTest6 = 
  createDistillationTest "linearAlgebraTests/addTransposeTranspose" "inputs/" "gold/linearAlgebra/addTransposeTranspose_gold" "inputs/" defaultTimeout

test_distillerLinearAlgebraTest7 :: IO TestTree
test_distillerLinearAlgebraTest7 = 
  createDistillationTest "linearAlgebraTests/mMult" "inputs/" "gold/linearAlgebra/mMult_gold" "inputs/" _10sec

test_distillerLinearAlgebraTest8 :: IO TestTree
test_distillerLinearAlgebraTest8 = 
  createDistillationTest "linearAlgebraTests/mapKron" "inputs/" "gold/linearAlgebra/mapKron_gold" "inputs/" defaultTimeout

test_distillerLinearAlgebraTest9 :: IO TestTree
test_distillerLinearAlgebraTest9 = 
  createDistillationTest "linearAlgebraTests/mAdd" "inputs/" "gold/linearAlgebra/mAdd_gold" "inputs/" defaultTimeout

test_distillerLinearAlgebraTest10 :: IO TestTree
test_distillerLinearAlgebraTest10 = 
  createDistillationTest "linearAlgebraTests/mEq" "inputs/" "gold/linearAlgebra/mEq_gold" "inputs/" _10sec