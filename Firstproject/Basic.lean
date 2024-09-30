def greet (name : String) := s!"Hello Lean, my name is {name}"

#eval greet "Federico"

-- Section 1.1

#eval 1 + 2
#eval 1 + 2 * 5
#eval 42 + 19

#eval String.append "Hello, " "Lean!"

#eval String.append "great " (String.append "oak " "tree")

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

#eval String.append "it is " "synthesized"

#eval String.append "A" (String.append "B" "C")

#eval String.append (String.append "A" "B") "C"

/-
As soon as the then branch is typed,
the Infoview suggests the same type for the else branch!
-/
#eval if 3 == 3 then 5 else 7

#eval if 3 == 4 then "equal" else "not equal"

-- Section 1.2

#eval (1 + 2 : Nat)

-- Subtraction over Nat does zero-truncation

#eval 1 - 2

-- To use a type that can represent the negative integers, provide it directly

#eval (1 - 2 : Int)

#check (1 - 2)

#check String.append "hello" [" ", "world"]

-- Section 1.3

def hello := "Hello"

def lean : String := "Lean"

#eval String.append hello (String.append " " lean)

def add1 (n : Nat) : Nat := n + 1
#eval add1 7

def maximum (n k : Nat) : Nat :=
  if n < k then k else n

#check add1
#check (add1)

#check maximum
#check (maximum)

#check maximum 3
#check String.append "Hello "
