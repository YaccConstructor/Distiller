{-# LANGUAGE InstanceSigs #-}

module Test.Generators where

import qualified Test.Tasty.Hedgehog
import qualified Hedgehog.Gen as Gen
import Hedgehog
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Term

genBool :: Gen Bool
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
natToTerm (Succ x) = Con "Succ" [natToTerm x]

test_natPropertyTestTree :: IO TestTree
test_natPropertyTestTree = return $ testGroup "Nat property tests"
   [ testProperty "(a + b) + c = a + (b + c)" associativePlusProp
   , testProperty "(a + b) - b = a" natPlusMinusProp
   , testProperty "(a * b) * c = a * (b * c)" associativeMulProp
   , testProperty "(toEnum (fromEnum a) = a)" natEnumProp
   , testProperty "Succ a >= a" greaterProp
   , testProperty "Pred a <= a" lessProp
    ]

natEnumProp :: Property
natEnumProp = property $ do
  a <- forAll genNat
  toEnum (fromEnum a) === a 

natPlusMinusProp :: Property
natPlusMinusProp = property $ do
  a <- forAll genNat
  b <- forAll genNat
  (a + b) - b === a 

associativePlusProp :: Property
associativePlusProp = property $ do
  a <- forAll genNat
  b <- forAll genNat
  c <- forAll genNat
  (a + b) + c  === a + (b + c)

associativeMulProp :: Property
associativeMulProp = property $ do
  a <- forAll genNat
  b <- forAll genNat
  c <- forAll genNat
  (a * b) * c  === a * (b * c)
  
greaterProp :: Property
greaterProp = property $ do
  a <- forAll genNat
  b <- (forAll . pure) $ succ a
  (b >= a) === True  
  
lessProp :: Property
lessProp = property $ do
  a <- forAll genNat
  b <- if a == Zero then (forAll . pure) Zero else (forAll . pure) $ pred a
  (b <= a) === True  