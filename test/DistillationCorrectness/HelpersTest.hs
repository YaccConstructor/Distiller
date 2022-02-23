module DistillationCorrectness.HelpersTest where
  
import Test.Tasty.Providers (TestTree)
import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TermType
import HelperTypes 

  
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

test_doBetaReductions :: IO TestTree
test_doBetaReductions = let
    term = Apply (Apply (Apply 
        (Lambda "x" (Lambda "y" (Lambda "z" (Case (Free "xs") 
            [("Nil",[], Con "Pair" [Free "x", Free "z"]), ("Cons", ["x","xs"], Free "y")])))) (Free "1")) (Free "2")) (Free "3")
    {---term' = Apply (Apply (Apply 
            (Lambda "x" (Lambda "y" (Lambda "z" (Case (Free "xs") 
                [("Nil",[], Con "Pair" [Free "x", Free "z"]), ("Cons", ["x","xs"], Free "y")])))) (Free "1")) (Free "2")) (Free "z")--}            
    result = Case (Free "xs") [("Nil",[], Con "Pair" [Free "1", Free "3"]), ("Cons", ["x","xs"], Free "2")]
    --result' = Case (Free "xs") [("Nil",[], Con "Pair" [Free "1", Free "3"]), ("Cons", ["x","xs"], Free "2")]
    in return $ testGroup "Helpers" [testCase "doBetaReductions" $ doBetaReductions term @?= result]
       --                             ,testCase "doBetaReductions" $ doBetaReductions term' @?= result']