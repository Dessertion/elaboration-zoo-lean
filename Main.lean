import ElaborationZoo
import ElaborationZoo.EvalClosuresNames

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let inputFile := (← stdin.getLine).trimAscii
  let src := (← IO.FS.readFile s!"./Inputs/{inputFile}.in")
  let ret ← parseString src
  stdout.putStrLn s!"{nf [] ret |>.prettify}"
