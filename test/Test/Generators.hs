{-# LANGUAGE InstanceSigs #-}

module Test.Generators where

import qualified Test.Tasty.Hedgehog
import qualified Hedgehog.Gen as Gen
import Hedgehog
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import TermType

{---genBool :: Gen Bool
genBool = Gen.bool

genListBool :: Gen [Bool]
genListBool = Gen.list (Range.linear 0 100) genBool

-- this type no implemented in Haskell yet except Data.Nat, which is dependent of QuickCheck 
data MyNat = Zero | Succ MyNat deriving (Eq, Ord, Show)

instance Num MyNat where
  Zero + y = y
  Succ x + y = Succ (x + y)
  
  Zero * y = Zero
  Succ x * y = y + (x * y)
 
  (-) Zero _         = Zero
  (-) x Zero         = x
  (-) (Succ x) (Succ y) = x - y

  abs x = x

  signum Zero = Zero
  signum _ = Succ Zero
  
  fromInteger 0 = Zero
  fromInteger n = Succ (fromInteger (n - 1)) 
  
instance Enum MyNat where
  pred :: MyNat -> MyNat
  pred Zero     = error "Zero has no predecessor."
  pred (Succ x) = x

  fromEnum :: MyNat -> Int
  fromEnum Zero     = 0
  fromEnum (Succ x) = 1 + fromEnum x

  toEnum :: Int -> MyNat
  toEnum 0 = Zero
  toEnum x
    | x > 0     = Succ $ toEnum (x - 1)
    | otherwise = error "Negative argument is prohibited."      

genNat :: Gen MyNat
genNat =  Gen.int (Range.constantFrom 0 0 10) >>= (return . toEnum)

genListNat :: Gen [MyNat]
genListNat = Gen.list (Range.linear 0 100) genNat

natToTerm :: MyNat -> Term
natToTerm Zero = Con "Zero" []
natToTerm (Succ x) = Con "Succ" [natToTerm x]--}