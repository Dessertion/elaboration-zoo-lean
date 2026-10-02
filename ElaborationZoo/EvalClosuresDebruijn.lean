import ElaborationZoo.Parser
import ElaborationZoo.Util

abbrev Idx := Nat
abbrev Lvl := Nat

inductive Tm where
  | var : Idx → Tm
  | lam : Tm → Tm -- \ (x . t)
  | app : Tm → Tm → Tm
  | let : Tm → Tm → Tm -- let t (x . u)
  deriving Repr, Inhabited

mutual

structure Closure where
  mk ::
  env : List (Thunk Val)
  tm  : Tm

inductive Val where
  | var : Lvl → Val
  | app : Val → Thunk Val → Val
  | lam : Closure → Val
  deriving Inhabited

end

-- an Env is just a list of lazy Vals
abbrev Env := List (Thunk Val)

mutual

partial def Closure.apply (cl : Closure) (u : Thunk Val) : Thunk Val :=
  let {env, tm} := cl
  tm.eval (u :: env)

partial def Tm.eval (env : Env) (tm : Tm) : Thunk Val := do
  match tm with
  | .var idx => env[idx]!
  | .lam t => return .lam (Closure.mk env t)
  | .app t u => do
    let u' := u.eval env
    let t' := t.eval env
    if let .lam cl := ← t' then
      cl.apply u'
    else
      return .app (← t') u'
  | .let t u =>
    u.eval (t.eval env :: env)

end

---------------------------------
-- normalization
---------------------------------

partial def quote (lvl : Lvl) (val : Val) : Tm :=
  match val with
  | .var l => .var (lvl - l - 1)
  | .app t u => .app (quote lvl t) (quote lvl u.get)
  | .lam cl => .lam (quote (lvl + 1) (cl.apply (pure <| .var lvl)).get)

def Tm.nf (env : Env) (tm : Tm) : Tm :=
  quote env.length (tm.eval env).get


---------------------------------
-- printing
---------------------------------

def Tm.prettify (tm : Tm) : String :=
  match tm with
  | .var idx => toString idx
  | .lam t => s!"λ {t.prettify}"
  | .app (.app t u) v => s!"{t.prettify} {u.prettify} {v.prettify}"
  | .app t u => s!"({t.prettify} {u.prettify})"
  | .let t u => s!"let {t.prettify};\n{u.prettify}"

---------------------------------
-- parsing
---------------------------------

def ex := String.intercalate "\n" [
  "let λ λ 1 (1 (1 (1 (1 0))));",    -- five = λ s z. s (s (s (s (s z))))
  "let λ λ λ λ 3 1 (2 1 0);",        -- add  = λ a b s z. a s (b s z)
  "let λ λ λ λ 3 (2 1) 0;",          -- mul  = λ a b s z. a (b s) z
  "let 1 2 2;",                      -- ten  = add five five
  "let 1 0 0;",                      -- hundred = mul ten ten
  "let 2 1 0;",                      -- thousand = mul ten hundred
  "0"                                -- thousand
  ]
-- #eval ex

/-
expr ::= let-expr | lambda-expr | debruijn-index
debruijn-index ::= ℕ
lambda-expr ::= "λ" expr+ | "\\" expr+
let-expr ::= "let" expr ";" expr
-/

def char c := Parser.lexeme <| .char c
def string s := Parser.lexeme <| .string s
def maybeParens (p : Parser Char α) : Parser Char α := Parser.parens p <|> p

mutual
partial def pTm : Parser Char Tm := do
  let tms ← Parser.takeWhile1P (pTmAtom <|>
    List.foldl1! Tm.app <$> (Parser.parens <| .takeWhile1P pTm))
  return List.foldl1! Tm.app tms

partial def pTmAtom : Parser Char Tm :=
  pLet <|> pLam <|> pIdx

partial def pIdx : Parser Char Tm := do
  let idx ← Parser.lexeme <| Parser.takeWhile1 Char.isDigit
  return .var <| (String.join <| idx.map Char.toString).toNat!

partial def pLam : Parser Char Tm := do
  let _ ← char '\\' <|> char 'λ'
  let u ← pTm
  return .lam u

partial def pLet : Parser Char Tm := do
  let t ← string "let" *> pTm
  let u ← char ';' *> pTm
  return .let t u
end

def pSrc := .ignore *> pTm <* .eof

def ex' := "let λ 1 (1 1) 1; 5"
def ex'' := "let λ λ 1 (1 (1 (1 (1 0))));
let λ λ λ λ 3 1 (2 1 0);
0 1 1"

def parseString' (str : String) : Tm :=
  match pSrc str.toList with
  | .ok t _ => t
  | .error _ _ => (.var 0)

-- #eval parseString' ex'' |>.nf [] |>.prettify
