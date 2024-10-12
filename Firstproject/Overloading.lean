/- Nonzero natural numbers. Although the definition
   is identical to that of Nat, Pos behaves differently
   in the definition of addition etc. -/
inductive Pos : Type where
  | one : Pos
  | succ : Pos -> Pos

/-- Overloaded notation and operations can't be
   synthesized for [Pos] -/
-- def seven : Pos := 7

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

-- def fourteen : Pos := seven + seven


/- A Lean's _method_ is an operation within a
   type class that has been declared to be overloadable. -/

/- Type classes are functions on types: they take
    a number of type argument for which overloaded
    operations are to be defined. Their application
    results in a new type that describes the overloaded
    operations that the class defines. -/
class Plus (α : Type) where
  plus : α → α → α

/- Overloading isn't done like this.
   This just extends the namespace with a new name. -/
def PlusNat := Plus Nat
def PlusNat.plus := Nat.add

#eval PlusNat.plus 2 3

-- ...but like this
instance : Plus Nat where
  plus := Nat.add

#eval Plus.plus 3 3

open Plus (plus) in
#eval plus 5 3

open Plus (plus)

def Pos.plus (n k : Pos) :=
  match n with
  | Pos.one => Pos.succ k
  | Pos.succ m => Pos.succ (m.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven

#eval plus 5.2 3.14

#eval plus (Pos.one) (Pos.one) -- fail because you haven't over implemented the [Repr] class for [Pos]
#eval fourteen

/- [Add] is for homogenous addition: both operands have the same type;
   [HAdd] is for heterogenous addition: the types of operands may differ;
   An instance of [Add] derives [HAdd]. -/

/- Ordinary addition syntax [+] is defined for [HAdd]
   and consequently for [Add]. To add two [Pos] values
   using the [+] symbol, instantiate [Add]. -/

instance : Add Pos where
  add := Pos.plus

def fifteen : Pos := seven + seven.succ

-- my attempt
def posToString' (atTop : Bool) (p : Pos) : String :=
  match p with
  | Pos.one => "1"
  | Pos.succ m =>
      if atTop
      then s!"succ ({posToString' false m})"
      else s!"succ {posToString' false m}"

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")" -- don't parenthesize the top costructor
  match p with
  | Pos.one => "one" -- neither the base case
  | Pos.succ m => paren s!"succ {posToString false m}"

#eval posToString' true seven
#eval posToString true seven

instance : ToString Pos where
  toString := posToString true

#eval ToString.toString seven

/- [toString] is the workhorse of string interpolation -/
#eval s!"There are {seven}" -- too verbose

/- Since every [Pos] has a corresponding [Nat],
   and pretty printing of [Nat] is terser,
   let's go through [Nat] to print a [Pos] -/
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ m => m.toNat + 1 -- Nat.succ (Pos.toNat m)

-- Takes over the older instance
instance : ToString Pos where
  toString p := toString (p.toNat)

#eval ToString.toString fourteen
#eval s!"There are {seven}"

-- Overloading [ToString] suffices to [#eval] a [Pos]
#eval seven
#eval fourteen
#eval seven + fourteen -- sum of [Pos]

/-
  [x + y] stands for [HAdd.hAdd x y]
  [x * y] stands for [HMul.hMul x y]
  [Mul] deals with homogenous multiplication
-/

def Pos.mul : Pos -> Pos -> Pos
  | Pos.one, k => k
  | Pos.succ m, k => k + m.mul k

instance : Mul Pos where
  mul := Pos.mul

#eval [seven * seven, seven * fourteen, Pos.one * seven]

-- Can we convey [Pos] values through number literals?

inductive LT3 where
  | zero
  | one
  | two
deriving Repr

#eval LT3.one

/- Type that the overloaded natural number literal
   should produce, and value for which it is defined -/
instance : OfNat LT3 0 where
  ofNat := LT3.zero

instance : OfNat LT3 1 where
  ofNat := LT3.one

instance : OfNat LT3 2 where
  ofNat := LT3.two

#eval 1
#eval (1 : LT3) -- We can write [0], [1], [2] wherever an [LT3] is expected.
#eval (3 : LT3) -- "failed to synthesize"

/- [n] is an automatic implicit argument.
   The instance is defined for a [Nat] that is one greater than [n].
   You can use [n] however you want to definition
   of [ofNat], which must be a [Pos]. -/
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat -> Pos
    | 0 => Pos.one
    | n + 1 => (natPlusOne n).succ
    natPlusOne n

#eval (0 : Pos)
#eval [(1 : Pos), 7, 10]

-- Now writing [Pos]'s is easy as cake

def eight : Pos := 8
-- def zero : Pos := 0
