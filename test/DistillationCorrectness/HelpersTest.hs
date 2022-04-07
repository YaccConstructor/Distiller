module DistillationCorrectness.HelpersTest where
  
import Test.Tasty.Providers (TestTree)
import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TermType
import DistillationHelpers

  
test_checkTermsRenaming1 :: IO TestTree
test_checkTermsRenaming1 = let
    term1 = Apply (Apply (Fun "f") (Free "xs'")) (Con "Cons" [Free "x", Free "x'"])
    term2 = Apply (Apply (Fun "f") (Free "xs")) (Free "x'")
    expected = [("x'",Con "Cons" [Free "x", Free "x'"]),("xs",Free "xs'")]
    in return $ testGroup "Helpers" [testCase "Renaming: f xs' Cons(x,x') and f xs x'" $ concat (termRenaming term2 term1) @?= expected]

test_checkTermsRenaming2 :: IO TestTree
test_checkTermsRenaming2 = let 
    term1 = Apply (Apply (Fun "f") (Apply (Fun "f'") (Free "y"))) (Con "Cons" [Free "x", Free "x'"])
    term2 = Apply (Apply (Fun "f") (Free "xs")) (Free "x")
    expected = [("x",Con "Cons" [Free "x", Free "x'"]),("xs", Apply (Fun "f'") (Free "y"))]
    in return $ testGroup "Helpers" [testCase "Renaming: f (f' y) Cons(x,x') and f xs x" $ concat (termRenaming term2 term1) @?= expected]
    
test_checkTermsRenaming3 :: IO TestTree
test_checkTermsRenaming3 = let 
    term1 = Apply (Fun "f") (Con "Cons" [Free "x", Free "x'"])
    term2 = Apply (Apply (Fun "f") (Free "xs")) (Free "x")
    in return $ testGroup "Helpers" [testCase "Renaming: f Cons(x,x') and f xs x" $ concat (termRenaming term2 term1) @?= []]
        
test_checkTermsRenaming4 :: IO TestTree
test_checkTermsRenaming4 = let 
    term1 = Apply (Fun "f") (Con "Cons" [Free "x", Free "x'"])
    term2 = Apply (Fun "f'") (Con "Cons" [Free "x", Free "x'"])
    in return $ testGroup "Helpers" [testCase "Renaming: f Cons(x,x') and f' Cons(x,x')" $ concat (termRenaming term2 term1) @?= []]

test_checkTermsRenaming5 :: IO TestTree
test_checkTermsRenaming5 = let 
    term = Apply (Apply (Fun "and") (Free "x")) (Con "False" [])
    in return $ testGroup "Helpers" [testCase "Renaming: and x False ; and x False" $ concat (termRenaming term term) @?= [("x",Free "x")]]

test_checkTermsRenaming6 :: IO TestTree
test_checkTermsRenaming6 = let
    term = Apply (Apply (Fun "append") (Free "xs")) (Free "ys")
    in return $ testGroup "HEChecker" [testCase "Renaming: append xs ys ; append xs ys" $ concat (termRenaming term term) @?= [("ys",Free "ys"),("xs",Free "xs")]]

test_doBetaReductions1 :: IO TestTree
test_doBetaReductions1 = let
    term = Apply (Apply (Apply 
        (Lambda "x" (Lambda "y" (Lambda "z" (Case (Free "xs") 
            [("Nil",[], Con "Pair" [Free "x", Free "z"]), ("Cons", ["x","xs"], Free "y")])))) (Free "1")) (Free "2")) (Free "3")            
    result = Case (Free "xs") [("Nil",[], Con "Pair" [Free "1", Free "3"]), ("Cons", ["x","xs"], Free "2")]
    in return $ testGroup "Helpers" [testCase "doBetaReductions1" $ doBetaReductions term @?= result]
       
test_doBetaReductions2 :: IO TestTree
test_doBetaReductions2 = let 
    term = Apply (Lambda "x" (Case (Free "xs''")  
                [("Nil",[], Con "Nil" [])
                ,("Cons", ["x'","xs'"], Con "Cons" [Free "x", Free "xs'"])])) (Con "Cons" [Free "x'", Free "xs'"])
    result = Case (Free "xs''") [("Nil",[],Con "Nil" []),("Cons",["x'","xs'"],Con "Cons" [Con "Cons" [Free "x'",Free "xs'"],Free "xs'"])]
    in return $ testGroup "Helpers" [testCase "doBetaReductions2" $ doBetaReductions term @?= result]

test_doBetaReductions3 :: IO TestTree
test_doBetaReductions3 = let
    term = Apply (Apply (Lambda "xs" (Lambda "ys" (Case (Free "xs")
            [("Nil",[], Free "xs")
            ,("Cons", ["x","xs#"], Free "xs#")]))) (Free "xs#")) (Free "ys")
    result = Case (Free "xs#") [("Nil",[],Free "xs#"),("Cons",["x","xs#"],Free "xs#")]
    in return $ testGroup "Helpers" [testCase "doBetaReductions3" $ doBetaReductions term @?= result]