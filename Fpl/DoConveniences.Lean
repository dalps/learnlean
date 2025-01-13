def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5

def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7

#eval getNumB

-- First snippet that doesn't work ☹
def test : IO Unit := do
  let a : Nat :=
    if (← getNumA) == 5 then 0 else (← getNumB)
  (← IO.getStdout).putStrLn s!"The answer is {a}"

#eval test

def test'' : IO Unit := do
  let x ← getNumA
  let y ← getNumB
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"

#eval test''
