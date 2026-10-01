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
