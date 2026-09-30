import Batteries.Control.AlternativeMonad
import Batteries.Data.Except

def ex1 := "\\x.x"
def ex2 := "(\\x.x) (\\x.x)"
def ex3 := "let five = \\s z. s (s (s (s (s z))));\
let add = \\a b s z. a s (b s z);\
let mul = \\a b s z. a (b s) z;\
let ten = add five five;\
let hundred = mul ten ten;\
let thousand = mul ten hundred;\
thousand"

abbrev Name := String
inductive Tm where
  | var : Name → Tm          -- x
  | lam : Name → Tm → Tm     -- \x. t
  | app : Tm → Tm → Tm       -- t u
  | let : Name → Tm → Tm     -- let x = t; u

-- Evaluation
------------------------

-- inductive Val where
--   | vvar : Name → Val
--   | vapp : Val → Val → Val
--   | vlam : Name → (Val → Val) → Val
