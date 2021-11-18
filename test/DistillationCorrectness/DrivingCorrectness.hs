module DistillationCorrectness.DrivingCorrectness where
  
import Driver
import LTSType
import TermType
import Test.Tasty
import Test.Tasty.HUnit

test_checkDrivingCorrectness1 :: IO TestTree
test_checkDrivingCorrectness1 = let
    expectedLts = LTS (LTSTransitions (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Free "xs")]) 
                        [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
                        ,(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))
                        ,(CaseBranch' "Cons" ["x","xs"],LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))])
    term1 = Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"], Free "xs")]
    in return $ testGroup "Tests" [testCase "lts1 from term1" $ drive term1 [] [] @?= expectedLts]

test_checkDrivingCorrectness2 :: IO TestTree
test_checkDrivingCorrectness2 = let 
    expectedLts = LTS (LTSTransitions 
                    (Case (Free "xs") [("Nil",[],Free "ys"),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))]) 
                        [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
                        ,(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))
                        ,(CaseBranch' "Cons" ["x","xs"], LTS (LTSTransitions 
                                                            (Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"])) 
                                                            [(Apply0',LTS (LTSTransitions 
                                                                (Apply (Fun "qrev") (Free "xs")) 
                                                                [(Apply0',LTS (LTSTransitions 
                                                                    (Fun "qrev") [(Unfold' "qrev",LTS (LTSTransitions 
                                                                        (Case (Free "xs") [("Nil",[],Free "ys")
                                                                                          ,("Cons",["x","xs"]
                                                                                          ,Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"]))
                                                                                          ]) 
                                                                        [(Case',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
                                                                        ,(CaseBranch' "Nil" [],LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))
                                                                        ,(CaseBranch' "Cons" ["x","xs"],LTS (LTSTransitions 
                                                                            (Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Free "ys"])) 
                                                                            [(Apply0',LTS (LTSTransitions 
                                                                                (Apply (Fun "qrev") (Free "xs")) 
                                                                                [(Apply0',LTS (LTSTransitions (Fun "qrev") [(Unfold' "qrev",Leaf)])),(Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))]))
                                                                            ,(Apply1',LTS (LTSTransitions 
                                                                                (Con "Cons" [Free "x",Free "ys"]) 
                                                                                [(Con' "Cons",Leaf),(ConArg' "#1",LTS (LTSTransitions (Free "x") [(X' "x",Leaf)])),(ConArg' "#2",LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))]
                                                                                )
                                                                             )
                                                                            ]))
                                                                        ]))])),
                                                                        (Apply1',LTS (LTSTransitions (Free "xs") [(X' "xs",Leaf)]))
                                                                ]))
                                                                ,(Apply1',LTS (LTSTransitions (Con "Cons" [Free "x",Free "ys"]) 
                                                                            [(Con' "Cons",Leaf)
                                                                            ,(ConArg' "#1",LTS (LTSTransitions (Free "x") [(X' "x",Leaf)]))
                                                                            ,(ConArg' "#2",LTS (LTSTransitions (Free "ys") [(X' "ys",Leaf)]))]))]))])
 


