module InputData where

import Generalizer
import Driver
import LTSType
import TermType
import Test.Tasty
import Test.Tasty.HUnit
import Debug.Trace (trace)  
  
qrevTerm = Case (Free "xs") [("Nil",[],Con "Cons" [Free "x", Con "Nil" []]),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x'",Con "Cons" [Free "x", Con "Nil" []]]))]
qrevLts = drive (Fun "qrev") [] [("qrev", (["xs", "ys"], qrevTerm))]
qrevTerm' = Case (Free "xs") [("Nil",[],Con "Nil" []),("Cons",["x","xs"],Apply (Apply (Fun "qrev") (Free "xs")) (Con "Cons" [Free "x",Con "Nil" []]))]
qrevLts' = drive (Fun "qrev") [] [("qrev", (["xs", "Nil"], qrevTerm'))]

swapQrevTerm = Case (Free "ys") [("Nil",[],Free "xs"),("Cons",["y","ys"],Apply (Apply (Fun "qrev") (Free "ys")) (Con "Cons" [Free "y",Free "xs"]))]
swapQrevLts = drive (Fun "qrev") [] [("qrev", (["xs", "ys"], swapQrevTerm))]
swapQrevTerm' = Case (Free "ys") [("Nil",[],Con "Nil" []),("Cons",["y","ys"],Apply (Apply (Fun "qrev") (Free "ys")) (Con "Cons" [Free "y",Con "Nil" []]))]
swapQrevLts' = drive (Fun "qrev") [] [("qrev", (["Nil", "ys"], swapQrevTerm'))]

appendTerm' = Case (Free "xs'")
    [("Nil",[],Con "Con" [Free "x'", Free "xs'"])
    ,("Cons",["x''","xs''"],Con "Cons" [Free "x''",Apply (Apply (Fun "append") (Free "xs''")) (Con "Con" [Free "x'", Free "xs'"])])]
appendLts' = drive (Fun "append") [] [("append", (["xs'", "Con(x',xs')"], appendTerm'))]
appendTerm = Case (Free "xs") [("Nil",[],Free "xs"),("Cons",["x'","xs'"],Con "Cons" [Free "x'",Apply (Apply (Fun "append") (Free "xs'")) (Free "xs")])]
appendLts = drive (Fun "append") [] [("append", (["xs", "xs"], appendTerm))]

neil3Term = Case (Apply (Fun "f") (Free "xs'"))    
                     [("True", [],Apply (Fun "f") (Free "xs'"))
                     ,("False", [], Con "False" [])]
neil3Def = Case (Free "xs")
    [("Nil",[], Con "True" [])
    ,("Cons",["x","xs"],Case (Apply (Fun "f") (Free "xs")) [("True", [], Apply (Fun "f") (Free "xs")), ("False",[], Con "False" [])])
    ]
neil3Lts = drive neil3Term [] [("f", (["xs"], neil3Def))]
neil3Term' = Case (Case (Apply (Fun "f") (Free "xs''"))    
                                        [("True", [],Apply (Fun "f") (Free "xs''"))
                                        ,("False", [], Con "False" [])])    
                     [("True", [],Apply (Fun "f") (Con "Con" [Free "x'", Free "xs''"]))
                     ,("False", [], Con "False" [])]
neil3Lts' = drive neil3Term' [] [("f", ([], neil3Def))]

  
