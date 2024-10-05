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

-- Lists

def primesUnder10 := [2, 3, 5, 7]

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

#eval explicitPrimesUnder10

def length (α : Type) (l : List α) :=
  match l with
  | List.nil => 0
  | List.cons _ l' => length α l' + 1

-- Implicit Arguments

def ireplace {α : Type} (point : PPoint α) (newX : α) :=
  { point with x := newX }

#eval ireplace natOrigin 5

def ilength {α : Type} (xs : List α) :=
  match xs with
  | [] => Nat.zero
  | _ :: ys => Nat.succ (ilength ys)

#eval ilength explicitPrimesUnder10
#eval explicitPrimesUnder10.length  -- stardard library's [length]

#check List.length (α := Int)

inductive Option' (α : Type) : Type where
  | none : Option' α
  | some (v : value) : Option' α

#eval List.head? ([] : List Nat)
#eval primesUnder10.head?
#eval [].headD 42 -- Default value helps infer α
#eval ([] : List Int).head? -- Type annotation
#eval [].head? (α := Int) -- Define α explicitly

#eval [].head?

def fives' : String × Int := { fst := "five", snd := 5 }

def fives := ("five", 5)

def sevens' : String × Int × Nat := ("VII", (7, 4 + 3))

-- Pairs are right associative: tuples are nested products behind the scenes.
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)

#eval fives.fst
#eval sevens.snd.snd

-- Better off defining a custom inductive datatype: dog names + cat names
def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Scooby", Sum.inr "Floppa", Sum.inr "Ray", Sum.inl "Billo", Sum.inr "Scratchy"]

def howManyDogs (pets : List PetName) :=
  List.filter (fun (p : PetName) =>
    match p with | Sum.inl _ => true
                 | Sum.inr _ => false) pets
  |> List.length

#eval howManyDogs animals

inductive ArithExpr (ann : Type) : Type :=
  | int : ann -> Int -> ArithExpr ann
  | plus : ann -> ArithExpr ann -> ArithExpr ann -> ArithExpr ann
  | minus : ann -> ArithExpr ann -> ArithExpr ann -> ArithExpr ann
  | times : ann -> ArithExpr ann -> ArithExpr ann -> ArithExpr ann

def noAnns := ArithExpr Unit

#check Unit.unit
#check ()
#check ArithExpr.int () (-2)
#check (ArithExpr.plus () (ArithExpr.int () (-2)) (ArithExpr.int () (-2)) : noAnns)

def left? {α : Type} (s : Sum α Empty) : Option α := s.getLeft?

#check Sum.inl true (β := Empty)
#eval left? (Sum.inl true)

/-
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType

inductive MyType : Type where
  | ctor : (MyType → Int) → MyType

inductive MyType (α : Type) : Type where
  | ctor : α → MyType

inductive MyType (α : Type) : Type where
  | ctor : α → MyType α

def ofFive : MyType := ctor 5
-/

def List.last {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [x] => x
  | _::ys => last ys

#eval primesUnder10.last

def List.findFirst? {α : Type} (xs : List α) (predicate : α -> Bool) :=
  match xs with
  | [] => none
  | y :: ys => if predicate y then some y
                              else ys.findFirst? predicate

#eval primesUnder10.findFirst? (fun x => even x)

def Prod.swap {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

#eval fives
#eval fives.swap

inductive PetName' : Type :=
  | DogName : String -> PetName'
  | CatName : String -> PetName'

def animals' : List PetName' := [
  PetName'.DogName "Scooby",
  PetName'.CatName "Floppa",
  PetName'.CatName "Ray",
  PetName'.DogName "Billo",
  PetName'.CatName "Scratchy"
]

def howManyDogs' (pets : List PetName') : Nat :=
  match pets with
  | [] => 0
  | PetName'.DogName _ :: ps => howManyDogs' ps + 1
  | PetName'.CatName _ :: ps => howManyDogs' ps


def zip {α β : Type} (as : List α) (bs : List β) : List (α × β) :=
  match as,bs with
  | [],_ | _,[] => []
  | a :: as', b :: bs' => (a,b) :: zip as' bs'

def primesWithPets := zip primesUnder10 animals

#eval primesWithPets
#check primesWithPets

def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n with
  | 0 => []
  | Nat.succ m => match xs with
                  | [] => []
                  | y :: ys' => y :: take m ys'

#eval take 0 animals
#eval take 2 animals
#eval take 8 animals

def distr {α β γ : Type} (pair : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match pair.snd with
  | Sum.inl b => Sum.inl (pair.fst, b)
  | Sum.inr c => Sum.inr (pair.fst, c)

#eval primesWithPets |> List.map distr

-- [Bool × α] and [α ⊕ α] have the same cardinality
def sumOfBoolPair {α : Type} (pair : Bool × α) : α ⊕ α :=
  if pair.fst then Sum.inl pair.snd else Sum.inr pair.snd

#eval sumOfBoolPair (true, 1)
#eval sumOfBoolPair (false, 1)

-- Let's complete the bijection
def boolPairOfSum {α : Type} (sum : α ⊕ α) : Bool × α :=
  match sum with
  | Sum.inl a => (true, a)
  | Sum.inr a => (false, a)

-- Section 1.7

-- You can leave out the implicit type argument
def length' (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length' ys)

-- Pattern-Matching definitions
def length'' : List α -> Nat
  | [] => 0
  | y :: ys => Nat.succ (length'' ys)

def drop : Nat -> List α -> List α
  | 0, xs               => xs
  | Nat.succ _, []      => []
  | Nat.succ n, _ :: xs => drop n xs

/- ^ is sugar for a match expression with simultaneous matching:

def drop (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n , y :: ys => drop n ys
-/

#eval drop 2 primesUnder10

def fromOption (default : α) : Option α -> α
  | none => default
  | some a => a

#eval (some "watermelon").getD "🍉"
#eval (some "西瓜").getD "🍉"
#eval none.getD "🍉"

-- Wasteful: O(2ⁿ) cons
def unzip'' : List (α × β) -> (List α × List β)
  | [] => ([],[])
  | (a,b) :: abs => (a :: (unzip'' abs).fst, b :: (unzip'' abs).snd)

-- Using a local definition: O(2n) cons
def unzip' : List (α × β) -> (List α × List β)
  | [] => ([],[])
  | (a,b) :: abs =>
      let u := unzip' abs -- newline separates let-expr and let-body (or [;] for single line)
      (a :: u.fst, b :: u.snd) -- it's a syntax error to indent the body further inward than the [let] keyword

-- Using a local definition + pattern matching
def unzip : List (α × β) -> (List α × List β)
  | [] => ([],[])
  | (a,b) :: abs =>
      let (as, bs) := unzip abs; (a :: as, b :: bs)

-- Like in OCaml, recursive [let] definition require the [rec] keyword
def reverse (xs : List α) : List α :=
  let rec helper acc : List α -> List α
    | [] => acc
    | y :: ys => helper (y :: acc) ys
  helper [] xs

#eval reverse primesUnder10


-- Omitting the return type of [unzip] is possible when using an explicit [match] expression. Omitting the argument type leads to an error.
def unzip''' (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x,y) :: xys =>
    let unzipped := unzip''' xys
    (x :: unzipped.fst, y :: unzipped.snd)

def even' : Nat -> Bool
  | 0 => true
  | n + 1 => ¬even n

def halve' : Nat -> Nat
  | 0 => 0
  | n + 2 => halve' n + 1
  | n + 1 => halve' n

def halve : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

#eval halve' 24
#eval halve 7

#check fun x => x -- Note the metavariables
#check fun (x : α) => x -- Wrong
-- Must provide a type argument for defining the identity
#check fun (α : Type) => fun (x : α) => x
#check fun {α : Type} => fun (x : α) => x
#check fun {α : Type} (x : α) => x -- curried
#check fun x => x + 1
#check fun (x : Int) => x + 1
#check λ x => x + 1
#check λ
      | 0 => none
      | n + 1 => some n

def double : Nat -> Nat
  | 0 => 0
  | n + 1 => double n + 2

#eval double 12

def double' : Nat -> Nat := fun
  | 0 => 0
  | n + 1 => double n + 2

-- Centered dot notation
#eval primesUnder10.map (. + 1)
#eval primesUnder10.map (double · + 2)

-- The centered dot always creates a function out of the _closest_ surrounding set of parentheses. Watch:
#check (· + 5, 3)
#check ((· + 5), 3)
#check (· , ·) 1 2

#eval (· + ·) 2 2
#eval (. * 2) 5


def Nat.double : Nat -> Nat := (· * 2)
#eval (4).double
#eval (4 : Nat).double

namespace Uple
def triple (x : Nat) := x * 3
def quadruple (x : Nat) := x * 4
end Uple

-- Locally-scoped [open]
def dodecaUple x :=
  open Uple in
  x |> triple |> quadruple

-- Command-scoped [open]
open Uple in
#check quadruple

-- Following commands still need qualification
#check triple

-- Top-level [open]
open Uple

#check quadruple
#check triple

inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline

-- Interested in a single constructor
def Inline.getString? : Inline -> Option String
  | string str => some str
  | _ => none

-- Pattern-matching with [if let]
def Inline.getString'? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none -- fallback

#eval ⟨1,2⟩ -- Type not obvious from the context
#eval (⟨1,2⟩ : Point)
#eval replaceX Nat ⟨1,2⟩ 3


#eval s!"three fours is {triple 4}"
#eval s!"three fours is {triple}"
