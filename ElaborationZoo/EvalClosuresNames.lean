import Batteries.Control.AlternativeMonad
import Batteries.Data.Except
import Batteries.Lean.EStateM
import ElaborationZoo.Parser

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
  | var : Name → Tm           -- x
  | lam : Name → Tm → Tm      -- \x. t
  | app : Tm → Tm → Tm        -- t u
  | let : Name → Tm → Tm → Tm -- let x = t; u
  deriving Repr, Inhabited

-- Evaluation
------------------------

mutual
  inductive Val where
    | vvar : Name → Val
    | vapp : Val → Val → Val
    | vlam : Closure → Val
    deriving Repr, Inhabited
  structure Closure where
    mk ::
    name : Name
    env  : List (Name × Val)
    term : Tm
    deriving Repr
end

abbrev Env := List (Name × Val)

partial def fresh (ns : List Name) (x : Name) : Name :=
  match x with
  | "_" => "_"
  | x =>
    bif ns.contains x then
      fresh ns (x ++ "'")
    else
      x

def freshCl (ns : List Name) (cl : Closure) : Name × Closure :=
  (fresh ns cl.name, cl)

mutual
partial def appCl : Closure → Val → Val
  | Closure.mk x env t, u => eval ((x, u) :: env) t

partial def eval (env : Env) : Tm → Val
  | .var x => env.lookup x |>.get!
  | .app t u =>
    let u := eval env u
    let t := eval env t
    if let .vlam cl := t then
      appCl cl u
    else
      .vapp t u
  | .lam x t => .vlam (Closure.mk x env t)
  | .let x t u => eval ((x, eval env t) :: env) u
end

partial def quote (ns : List Name) : Val → Tm
  | .vvar x => .var x
  | .vapp t u => .app (quote ns t) (quote ns u)
  | .vlam cl =>
    let (x, cl) := freshCl ns cl
    .lam x (quote (x :: ns) (appCl cl (.vvar x)))

def nf (env : Env) : Tm → Tm :=
  quote (env.map Prod.fst) ∘ eval env

-- λ x. x
def ex1' : Tm := .lam "x" (.var "x")
-- (λ x. x) (λ x. x)
def ex2' : Tm := .app (.lam "x" (.var "x")) (.lam "x" (.var "x"))

-- #eval nf [] ex1'
-- #eval nf [] ex2'

-- printing
--------------------------

def showParen (p : Bool) (s : String) : String :=
  bif p then s!"({s})" else s

def Tm.prettify (t : Tm) : String :=
  let rec go : Bool → Tm → String :=
    fun p t =>
      match t with
      | .var x => x
      | .app (.app t u) u' =>
        showParen p s!"{go false t} {go true u} {go true u'}"
      | .app t u =>
        showParen p s!"{go true t} {go true u}"
      | .lam x t =>
        showParen p s!"λ {x}. {go False t}"
      | .let x t u =>
        s!"let {x}\n    = {go False t}\n;\n{go False u}"
  go false t

-- #eval ex1'.prettify
-- #eval ex2'.prettify
-- #eval nf [] ex2' |>.prettify

instance Tm.instToString : ToString Tm := ⟨Tm.prettify⟩

-- parsing
----------------------------


def isKeyword (s : String) : Bool :=
  s == "λ" || s == "in" || s == "let"

def char c := Parser.lexeme <| .char c
def symbol s := Parser.lexeme <| .string s

-- an ident is [a-zA-Z][a-zA-Z0-9]*
def pIdent : Parser Char Name := do
  try
    let ret ←
      .lexeme <| (List.cons · []) <$> .satisfy Char.isAlpha >> .takeWhile Char.isAlphanum
    let s := String.ofList ret
    if isKeyword s then
      throw <| .customError s!"{s} is a keyword, not a valid ident."
    else
      return s
  catch e =>
    throw e

def pBind := pIdent <|> symbol "_"

def List.foldl1 (f : α → α → α) : List α → Option α
  | [] => .none
  | x :: xs => .some (xs.foldl f x)

def List.foldl1! [Inhabited α] (f : α → α → α) : List α → α
  | [] => panic "womp womp"
  | x :: xs => xs.foldl f x

mutual
partial def pAtom := (Tm.var <$> pIdent) <|> Parser.parens pTm
partial def pSpine := List.foldl1! Tm.app <$> Parser.takeWhile1P pAtom

partial def pLam : Parser Char Tm := do
  let _ ← char 'λ' <|> char '\\'
  let xs ← Parser.takeWhile1P pBind
  let _ ← char '.'
  let t ← pTm
  return (List.foldr Tm.lam t xs)

partial def pLet : Parser Char Tm := do
  let x ← symbol "let" *> pBind <* char '='
  let t ← pTm <* char ';'
  let u ← pTm
  return Tm.let x t u

partial def pTm : Parser Char Tm := pLam <|> pLet <|> pSpine
end

def pSrc := .ignore *> pTm <* .eof

def parseString (src : String) : IO Tm := do
  match pSrc src.toList with
  | .ok t _ => pure t
  | .error e _ =>
    (← IO.getStdout).putStrLn s!"{repr e}"
    IO.Process.exit 1

/-
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let inputFile := (← stdin.getLine).trimAscii
  let src := (← IO.FS.readFile s!"./Inputs/{inputFile}.in")
  let ret ← parseString src
  stdout.putStrLn s!"{nf [] ret |>.prettify}"
-/
