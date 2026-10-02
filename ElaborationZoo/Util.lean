def List.foldl1 (f : α → α → α) : List α → Option α
  | [] => .none
  | x :: xs => .some (xs.foldl f x)

def List.foldl1! [Inhabited α] (f : α → α → α) : List α → α
  | [] => panic "womp womp"
  | x :: xs => xs.foldl f x

instance : Monad Thunk where
  pure := Thunk.pure
  bind := Thunk.bind
