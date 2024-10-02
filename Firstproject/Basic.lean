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

-- Structures are defined by a single constructor

structure Point3D where
  point ::
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

-- A [structure] declaraction both declares a type and places its _names_ in a _namespace_ named after the declared type

#check Point.mk 1.5 2.8
#check Point3D.point 1.0 0.2 3e-2

#check (Point.x)

#eval origin.x
-- stands for:
#eval Point.x origin

-- Accessor notation + functions
#eval "one string".append " and another"

def Point.modifyBoth (ψ : Float -> Float) (π : Point) : Point :=
  { x := ψ π.x, y := ψ π.y }

-- The target of the accessor is used as the first argument in which the type matches (not necessarily the first argument)

def p₁ : Point := { x := 4.32 , y := 3.0 }

#eval p₁.modifyBoth Float.floor

/- Note: a function applied to a target value using the accessor notation must be defined under the namespace named after the target's type.
-/

#eval (Float.floor).modifyBoth p₁

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr

def RectangularPrism.volume (p : RectangularPrism) : Float :=
  p.height * p.width * p.depth

structure Segment where
  pStart : Point
  pEnd : Point
deriving Repr

def Segment.length (s : Segment) : Float :=
  distance s.pStart s.pEnd

def σ : Segment := { pStart := origin, pEnd := p₁ }

#eval σ.length

structure Hamster where
  name : String
  fluffy : Bool

#check (Hamster.mk)

structure Book where
  makeBook :: -- custom name for constructor
  title : String
  author : String
  price : Float

#check (Book.makeBook)


-- Section 1.5

-- _Recursive sum types_ are called _inductive types_

inductive Bool' where
  | false : Bool'
  | true : Bool'

-- Inductive datatypes may define multiple constructors

def isZero  (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

#eval isZero Nat.zero
#eval isZero 45

#eval Nat.pred 0

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 5

def depth (p : Point3D) : Float :=
  match p with
  | { x := _ , y := _ , z := d } => d

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ n => not (even n)

#check not

def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (evenLoops n)

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

#eval (times 5 (minus 7 3))

def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else
    /- The recursive invocation of the
       function call is applied to _the
       result of another function call_,
       rather than to an input
       constructor's argument -/
    Nat.succ (div (n - k) k)

-- Section 1.6

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero , y := Nat.zero }

def replaceX (α : Type) (p : PPoint α) (newX : α) :=
  { p with x := newX }

#eval replaceX _ natOrigin 3

/-
  This type is a function in itself: the type of [replaceX Nat]
  is found by replacing all occurences of [α] with the provided
  value [Nat] in the function's return type [PPoint α → α → PPoint α].

  replaceX : (α : Type) → PPoint α → α → PPoint α
-/
#check (replaceX)

#check replaceX Nat
#check replaceX Nat natOrigin
#check replaceX Nat natOrigin 4

/-
  Polymorphic functions work by taking a named
  type argument and having later types refer to the argument's name. -/

inductive Sign where
  | pos
  | neg

-- Good example of dependent types

def posOrNegTwo (s : Sign) :
  match s with | Sign.pos => Nat
               | Sign.neg => Int :=
  match s with
  | Sign.pos => 2
  | Sign.neg => -2

#eval posOrNegTwo Sign.neg
#check posOrNegTwo Sign.pos
