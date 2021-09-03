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
import qualified Data.Foldable as List

substituteAll :: Foldable t => Term -> t (String, Term) -> Term
substituteAll =
    foldl (\ term (name, subst_term) -> subst subst_term (abstract term name)) 

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
test_plusMinus_2_property = do createTest "plusMinus_2" "inputs/" plusMinus_2 defaultTimeout 
    where
    plusMinus_2 (origMainTerm, origTerms) (distilledMainTerm, distilledTerms) = do (p1,p2)
        where 
        getEvalResults m n = let n_term = natToTerm n
                                 m_term = natToTerm m
                                 substitutions = [("n", n_term), ("m", m_term)]
                                 origResults = Term.eval (substituteAll origMainTerm substitutions) EmptyCtx origTerms 0 0            
                                 distilledResults = Term.eval (substituteAll distilledMainTerm substitutions)  EmptyCtx distilledTerms 0 0
                             in (origResults, distilledResults)

        p1 = property $ do  n <- forAll genNat
                            m <- forAll genNat
                            let ((origRes, _1,_2), (distilledRes, _3,_4)) = getEvalResults m n
                            origRes === distilledRes
        p2 = property $ do  n <- forAll genNat
                            m <- forAll genNat
                            let ((_1, origReductions, origAllocations), (_2, distilledReductions,distilledAllocations)) = getEvalResults m n
                            (origReductions >= distilledReductions && origAllocations >= distilledAllocations) === True
        

test_plusMinus_1_property :: IO TestTree
test_plusMinus_1_property = do createTest "plusMinus_1" "inputs/" plusMinus_2 defaultTimeout 
    where
    plusMinus_2 (origMainTerm, origTerms) (distilledMainTerm, distilledTerms) = do (p1,p2)
        where 
        getEvalResults m n = let n_term = natToTerm n
                                 m_term = natToTerm m
                                 substitutions = [("n", n_term), ("m", m_term)]
                                 origResults = Term.eval (substituteAll origMainTerm substitutions) EmptyCtx origTerms 0 0            
                                 distilledResults = Term.eval (substituteAll distilledMainTerm substitutions)  EmptyCtx distilledTerms 0 0
                             in (origResults, distilledResults)

        p1 = property $ do  n <- forAll genNat
                            m <- forAll genNat
                            let ((origRes, _1,_2), (distilledRes, _3,_4)) = getEvalResults m n
                            origRes === distilledRes
        p2 = property $ do  n <- forAll genNat
                            m <- forAll genNat
                            let ((_1, origReductions, origAllocations), (_2, distilledReductions,distilledAllocations)) = getEvalResults m n
                            (origReductions >= distilledReductions && origAllocations >= distilledAllocations) === True    
    