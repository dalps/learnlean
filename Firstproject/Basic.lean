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

def joinStringsWith (s1 s2 s3 : String) : String := String.append s2 (String.append s1 s3)

#eval joinStringsWith ", " "one" "and another"

#check joinStringsWith ": "

def volume (x y z : Nat) := x * y * z

#eval volume 3 4 5
#eval volume 3 3 3
#check volume 1 1


def Str : Type := String

def aStr : Str := "Yet another string."


def NaturalNumber : Type := Nat

def fortyTwo_bad : NaturalNumber := 42

def fortyTwo : NaturalNumber := (42 : Nat)

abbrev N : Type := Nat

def thirtyNine : N := 39

-- Section 1.4

#check 0

#check (0 : Float)

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := {x := 0.0, y := 0.0}

#eval origin
#eval origin.x
#eval origin.y

def addPoints (p1 p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

def distance (p1 p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance origin (addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 })

#eval distance { x := 1.0 , y := 2.0 } { x := 5.0 , y := -1.0 }


structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

-- The structure's expected type must be known in order to use the curly-brace syntax
def origin3D : Point3D := { x := 0.0 , y := 0.0 , z := 0.0 }

#check ({ x := 0.0, y := 0.0 } : Point)
#check { x := 0.0, y := 0.0  : Point}


def zeroX_long (p : Point) : Point :=
  { x := 0, y := p.y }

def zeroX (p : Point) : Point :=
  { p with x := 0 }

def zeroXY3D (p : Point3D) :=
  { p with x := 0, y := 0 }

-- Continue from "Behind the Scenes"
