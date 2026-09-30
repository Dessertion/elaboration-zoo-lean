import Batteries.Control.AlternativeMonad
import Batteries.Data.Except
import Batteries.Lean.EStateM

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

partial def fresh (ns : List Name) : Name → Name
  | "_" => "_"
  | x =>
    bif ns.contains x then
      fresh ns (x ++ "''")
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

#eval nf [] ex1'
#eval nf [] ex2'

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

#eval ex1'.prettify
#eval ex2'.prettify
#eval nf [] ex2' |>.prettify

instance Tm.instToString : ToString Tm := ⟨Tm.prettify⟩

-- parsing
----------------------------

-- kill me.
/-- `ι` is the type of input. -/
inductive Error (ι : Type u) where
  | endOfInput  : Error ι          -- Expected more input, but there is nothing
  | unexpected  : ι → Error ι      -- We didn't expect to find this element
  | customError : String → Error ι -- User-generated error message.
  | failure                        -- I have no clue.
  deriving DecidableEq, Repr, BEq

-- Parser ι α should be List ι → α × List ι
-- StateM σ α := σ → α × σ
@[always_inline]
abbrev Parser ι := EStateM (Error ι) (List ι)

namespace Parser

/-
instance instBacktrackable (ι : Type u) : EStateM.Backtrackable (List ι) (List ι) where
  save := id
  restore _ snapshot := snapshot
-/

def satisfy (predicate : ι → Bool) : Parser ι ι := do
  match ← get with
  | [] => throw .endOfInput
  | x :: xs =>
    bif predicate x then do
      set xs
      return x
    else
      throw <| .unexpected x

def fail : Parser ι α := do
  throw .failure

def andThen {α : Type u} (p q : Parser ι (List α)) : Parser ι (List α) := do
  return (← p) ++ (← q)

instance instAndThen : AndThen (Parser ι (List α)) where
  andThen p q := do
    let p_ret ← p
    let q_ret ← q ()
    return p_ret ++ q_ret

partial def takeWhileP (p : Parser ι α) : Parser ι (List α) := do
  let rec takeWhileAux : List α → Parser ι (List α) := fun l =>
    tryCatch
      (do let ret ← p; takeWhileAux (ret :: l))
      (fun _ => return l)
  return (← takeWhileAux []).reverse

def takeWhile (predicate : ι → Bool) : Parser ι (List ι) :=
  takeWhileP (satisfy predicate)

/-- `takeWhile1P` is takeWhileP, but must succeed at least once or else fails. -/
def takeWhile1P (p : Parser ι α) : Parser ι (List α) := do
  let ret ← takeWhileP p
  if let [] := ret then
    throw <| Error.failure
  else
    return ret

def takeWhile1 (predicate : ι → Bool) :=
  takeWhile1P (satisfy predicate)

def takeTill (predicate : ι → Bool) : Parser ι (List ι) :=
  takeWhile (not ∘ predicate)

def char [DecidableEq ι] (c : ι) : Parser ι ι :=
  satisfy (· = c)

def anyChar : Parser ι ι :=
  satisfy (fun _ => true)

def peekChar : Parser ι ι := do
  match ← get with
  | [] => throw .endOfInput
  | x :: _ => return x

def list [DecidableEq ι] (l : List ι) : Parser ι (List ι) :=
  match l with
  | [] => pure []
  | x :: xs => do
    let y ← char x
    let ys ← list xs
    return (y :: ys)

def skipWhileP (p : Parser ι α) : Parser ι Unit := do
  let _ ← takeWhileP p

def skipWhile (predicate : ι → Bool) : Parser ι Unit := do
  let _ ← takeWhile predicate

/-- `choice ps` tries to apply the parsers in `ps` in order, until one of them succeeds,
whence it returns the value of the suceeding action. -/
def choice (ps : List (Parser ι α)) : Parser ι α :=
  ps.foldl (· <|> ·) fail

def string (s : String) : Parser Char String := do
  return String.ofList (← list s.toList)

def ws1 : Parser Char Unit := do
  let _ ← satisfy Char.isWhitespace

def ws : Parser Char Unit :=
  skipWhileP ws1

def lineComment : Parser Char Unit := do
  ws <* string "--" <* takeWhile (· != '\n') <* char '\n'

def ignore : Parser Char Unit := do
  let _ ← takeWhileP (ws1 <|> lineComment)

def lexeme {α} (p : Parser Char α) : Parser Char α := do
  ignore *> p <* ignore

def parens {α} (p : Parser Char α) : Parser Char α := do
  lexeme <| char '(' *> p <* char ')'

def eof : Parser ι Unit :=
  try
    let ret ← anyChar
    throw <| .unexpected ret
  catch _ =>
    return

end Parser

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
