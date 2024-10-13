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

-- # Exercises

namespace Exercise1
-- ~20 min

structure Pos where
  succ :: -- constructor's name, overrides [mk]
  pred : Nat
deriving Repr

#check Pos.succ
#check Pos.succ 1

instance : OfNat Pos (n + 1) where
  ofNat := ⟨n⟩

    /- You're dumb

    let rec natPlusOne : Nat -> Pos
    | 0 => ⟨1⟩ -- [\lan] and [\ran]
    | n + 1 => Pos.succ (natPlusOne n).pred
    natPlusOne n -/

def seven : Pos := 7
def one : Pos := 1

#eval one
#eval seven

def Pos.add (n k : Pos) : Pos := ⟨n.pred + k.pred + 1⟩

instance : Add Pos where
  add := Pos.add

#eval seven + one
#eval seven + seven

-- (n + 1) * (k + 1) = n * k + n + k + 1
def Pos.mul (n k : Pos) : Pos := ⟨(n.pred + 1) * (k.pred + 1) - 1⟩

instance : Mul Pos where
  mul := Pos.mul

def fortynine : Pos := seven * seven
#eval fortynine

instance : ToString Pos where
  toString p := toString (p.pred + 1)

#eval s!"There are {seven}"
#eval s!"{fortynine} cats and {seven + 1} dogs."

end Exercise1

namespace Exercise2
-- 27:46 min

inductive IsEven : Nat → Prop
  | zero : IsEven 0
  | ss (e : IsEven n) : IsEven (n + 2)

structure Even where
  half : Nat
deriving Repr

def Even.add (n k : Even) : Even := ⟨n.half + k.half⟩
def Even.mul (n k : Even) : Even := ⟨2 * n.half * k.half⟩

instance : Add Even where
  add := Even.add

instance : Mul Even where
  mul := Even.mul

instance : ToString Even where
  toString e := toString (2 * e.half)


def two : Even := ⟨1⟩
def six : Even := ⟨3⟩
def eight : Even := ⟨4⟩
def fortytwo : Even := ⟨21⟩

def fourteen := six + eight

#eval six + eight
#eval s!"♩{fortytwo + two} gatti in fila per {six} col resto di {(⟨1⟩ : Even)}♩"

end Exercise2

namespace Exercise3
-- 55:31 min; instructions unclear + incompetence of mine + head scratching

-- See https://developer.mozilla.org/en-US/docs/Web/HTTP/Messages

inductive HTTPMethod
  | get
  | post (body : String)
deriving Repr

/- This wasn't requested by the exercise
   Wasted a lot of time trying to retrofit it in
   the type class. In fact, it obviates the need
   for a type class. >:(
-/
structure HTTPRequest where
  method : HTTPMethod
  version : String
  uri : String
deriving Repr

structure HTTPResponse where
  version : String
  status : Nat
  body : Option String

instance : ToString HTTPResponse where
  toString r := s!"
http version :: {r.version}
status       :: {r.status}
payload      :: {r.body}"

class Server (m : HTTPMethod) where
  reply : IO HTTPResponse

instance : Server HTTPMethod.get where
  reply := do
    IO.println "sup"
    pure ⟨"HTTP/1.1", 404, Option.some "idk"⟩

instance : Server (HTTPMethod.post body) where
  reply := do
    IO.println "nice body"
    pure ⟨"HTTP/1.1", 200, Option.some s!"
<html>
  <body>
    <p align='center'>{body}</p>
  </body>
</html>"⟩

-- My test harness
#eval Server.reply HTTPMethod.get
#eval Server.reply (HTTPMethod.post "hello world")

-- Still not convinced this is what they're asking

-- "Use a type class to associate different IO actions with each HTTP method"

class Client (α : Type) where
  send : IO α -> HTTPMethod

end Exercise3

-- [IO.println] prints any value whose type there is an instance of [ToString]
#eval IO.println "foo"
#eval IO.println (some "foo")
#eval IO.println 3
#eval IO.println true

#check IO.println
#check @IO.println

-- ## Instance Implicits

def List.sum [Add α] [OfNat α 0] : List α -> α
  | [] => 0
  | x :: xs => x + xs.sum

def fourNats : List Nat := [2, 3, 5, 7]

#eval fourNats.sum

def fourPos : List Pos := [2, 3, 5, 7]

#eval fourPos.sum -- error

/- Key points
  1. A type class defines a structure that has a field for each overloaded operation. Instances are values of that structure type. Values of the fields contain the impementation for the instance.
  2. A function definition can include instance implicits, which add constraints on implicit polymorphic type arguments (see [List.sum] example)
  3. At call site, the strategy Lean uses to discover implicit instances is different from that of implicit arguments. While the latter are determined through unification, for instance implicit Lean consults a built-in table of instance values
  4. Instances may also take instance implicits arguments (see [PPoint.sum] example)
  5. A recursive instance search results in a structure value that has a reference to another structure value. For example, the instance value of [Add (PPoint Nat)] carries a reference to [Add Nat].
 -/

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

/- The colon [:] separate the instance's arguments
   from the return type -/
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

/- Recall the definition of the type class [OfNat]:

  class OfNat (α : Type) (_ : Nat) where
    ofNat : α
-/
#check OfNat
#check @OfNat
#check OfNat.ofNat
#check @OfNat.ofNat -- note the explicit [Nat] argument [n]. It wasn't part of the user signature of the method, it was introduces by Lean to help itself figure out the instance value

/-
  Just as accessor methods of ordinary structure types take a value of the structure type as argument, type class instance methods take an instance implicit as argument (often called [self]).
-/
#check @Add.add

namespace Exercise4
-- ~10 min

open Exercise2

instance : OfNat Even Nat.zero where
  ofNat := ⟨0⟩

-- It isn't as simple as (n * 2)
instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := ⟨(n + 2) / 2⟩

def four : Even := 4

#eval four
#eval (254 : Even)
#eval (3 : Even)
#eval (42 : Even)
#eval four + 18
#eval four * 102
#eval (254 : Even)
#eval (256 : Even) -- the search limit seems to be around 128

end Exercise4

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => (addNatPos n p).succ

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => (addPosNat p n).succ

#eval addNatPos 9 9
#eval addPosNat 18 0

#check @Add.add
#check @HAdd.hAdd

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (7 : Nat) + seven
#eval seven + (7 : Nat)
#eval (3 : Pos) + (5 : Nat)

namespace UselessHPlus

class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

#eval HPlus.hPlus seven (7 : Nat) -- typechecker panics: "typeclass instance problem is stuck"

#eval HPlus.hPlus (7 : Nat) (3 : Pos)

-- The typechecker needs more hand-holding
#eval (HPlus.hPlus (7 : Nat) (3 : Pos) : Pos)
#eval (HPlus.hPlus (7 : Pos) (3 : Nat) : Pos)

end UselessHPlus

/- Having to specify the return type of addition defeats the purpose of overloading. [HPlus] is too weak. -/

/- The trick is to instruct the instance search
  algorithm to start the search without knowing [γ] in advance (i.e. leave it as a metavariable), and try to discover it in the process. This is possible by marking its type as [outParam].
-/

-- This is how Lean's [HAdd] is defined
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

#eval HPlus.hPlus (7 : Nat) (3 : Pos)
#eval HPlus.hPlus (7 : Pos) (3 : Nat)

-- Default instances

instance [Add α] : HPlus α α α where
  hPlus := Add.add

-- Now [hPlus] can be used for any addable type
#eval HPlus.hPlus (3 : Nat) (5 : Nat)
#check HPlus.hPlus (3 : Nat) (5 : Nat)

-- Type class search occurs even when some inputs are unknown
#check HPlus.hPlus (3 : Nat) -- note the metavariables: the search algorithm started, and it is waiting for more information

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

-- [@[default_instance]] instructs the search algorithm to fill out the holes with the information provided by the type-homogenous instance.

#check HPlus.hPlus (5 : Nat) -- [Nat -> Nat]: the default instance was selected

#check 5 -- [Nat]: this judgment is also due to the instance of [OfNat] for [Nat] being marked as the default one

namespace Exercise5

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p n:= { x := p.x * n, y := p.y * n }

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0

end Exercise5

def northernTrees : Array String :=
  #["sloe", "birch", "spruce", "oak"]

#eval northernTrees[8]?
#eval northernTrees[2]

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobe Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmptyList α -> Nat -> Option α
  | xs, 0 => some xs.head
  | { head := _, tail := [] }, _ + 1 => none
  | { head := _, tail := x :: xs }, n+1 =>
    get? { head := x, tail := xs } n

#eval idahoSpiders.get? 1
#eval idahoSpiders.get? 5

def NonEmptyList.getL? : NonEmptyList α -> Nat -> Option α
  | xs, 0 => some xs.head
  | { head := _, tail := xs }, n + 1 => xs.get? n

#eval idahoSpiders.getL? 0
#eval idahoSpiders.getL? 4

/- A type constructor defined with [abbrev] so that tactics
   in charge ofbound checking know to automatically unfold it. -/
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i <= xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 :=
  by simp! -- Idk why I need to use the bang

theorem notSixSpiders : ¬idahoSpiders.inBounds 5 :=
  by simp!

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]'ok -- Indexes are zero-based: [i] might be illegal for the tail
  -- Lean automatically derives [n < xs.tail.length], needed for access to [List], from the evidence [ok : n + 1 <= xs.tail.length]

#check @GetElem
#check @GetElem.getElem

instance {α : Type} : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

-- This is amazing
#eval idahoSpiders[0]
#eval idahoSpiders[4]
#eval idahoSpiders[3]!
#eval idahoSpiders[5]?

instance : GetElem (List α) Pos α (fun xs p => p.toNat < xs.length) where
  getElem := fun xs p ok => xs[p.toNat]'ok

def primesTil7 : List Nat := [2, 3, 5, 7]
def one : Pos := 1

#eval primesTil7[one]
#eval primesTil7[(2 : Pos)]

/- [false] selects [x], [true] selects [y].
   Evidence is vacuous here, since every boolean is a valid index. -/
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem
  | p, true, _ => p.y
  | p, false, _ => p.x

def p1 := {x := 2.5, y := 3.7 : PPoint Float}

#eval p1[false]
#eval p1[true]

/- [==] is the overloaded operator for _Boolean equality_ -/
#eval "Octopus" == "Octocat"
#eval (fun (x : Nat) => 1 + x) == Nat.succ

theorem xPlusOne_eq_succ : (fun (x : Nat) => 1 + x) = Nat.succ :=
  by
    funext x
    simp
    apply Nat.add_comm

-- [if] works with both boolean values and _decidable_ propositions
#eval if true then "Yes" else "No"
#eval if 2 == 2 then "Yes" else "No" -- Boolean equality
#eval if 2 = 2 then "Yes" else "No" -- Prop equality
#eval if 2 < 4 then "Yes" else "No"

/- The example above work because equality and less-than
   relations over [Nat]s are decidable, i.e. they are
   instances of the [Decidable] type class.

   Indeed, propositions that are instances of [Decidable]
   can be reflected into a [Bool], hence [if] notation can be
   overloaded for such propositions.

   On the other hand, equality over [Nat -> Nat] is not
   decidable, so a statement like [xPlusOne_eq_succ] can't
   be used as the condition of [if]. -/

#eval if (fun (x : Nat) => 1 + x) = Nat.succ then "Yes" else "No"

def Pos.comp : Pos → Pos → Ordering
  | 1, 1 => Ordering.eq
  | 1, succ _ => Ordering.lt
  | succ _, 1 => Ordering.gt
  | succ n, succ k => n.comp k

instance : ToString Ordering where
  toString
  | Ordering.eq => "eq"
  | Ordering.lt => "lt"
  | Ordering.gt => "gt"

#eval Pos.comp seven fourteen

instance : Ord Pos where
  compare := Pos.comp

#eval Ord.compare seven fourteen
#eval Ord.compare fourteen (seven + 1)

-- Exercise: overload [Ordering] for [Point] using the distance from the origin

-- # Hashing

def hashPos : Pos -> UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

#eval Hashable.hash (1 : Pos)
#eval Hashable.hash (4 : Pos)
#eval Hashable.hash fourteen

-- [mixHash] is used to combine hashes for different fields for a constructor
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (Hashable.hash xs.head) (Hashable.hash xs.tail)

#eval Hashable.hash idahoSpiders

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α -> α -> BinTree α -> BinTree α

/- Boolean equality for binary tree can be implementend provided
   the elements also implement [BEq], motivating the use of
   recursive instance search. -/
def BinTree.eq [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf => true
  | BinTree.leaf, _
  | _, BinTree.leaf => false
  | BinTree.branch l1 a1 r1, BinTree.branch l2 a2 r2 =>
    a1 == a2 && l1.eq l2 && r1.eq r2

instance [BEq α] : BEq (BinTree α) where
  beq := BinTree.eq

open BinTree (leaf branch)
#eval leaf == branch leaf 1 leaf
#eval branch leaf 1 leaf == branch leaf 1 leaf
#eval branch (branch leaf 2 leaf) 1 leaf == branch leaf 1 (branch leaf 2 leaf)

def BinTree.hash [Hashable α] : BinTree α -> UInt64
  | leaf => 0
  | branch l a r => mixHash l.hash (mixHash (Hashable.hash a) r.hash)

instance [Hashable α] : Hashable (BinTree α) where
  hash := BinTree.hash

#eval Hashable.hash (branch (branch leaf 2 leaf) 1 leaf)
#eval Hashable.hash (branch (branch leaf 3 leaf) 1 leaf)
#eval Hashable.hash (branch leaf 1 (branch leaf 3 leaf))

/- This was quite tedious to implement by hand!

   Lean is able to _derive_ instances of Standard type classes
   for user types. In the example of [Point] we derived the class
   [Repr] in locus of defining the structure type.

   This class let us display [Point] values in the Infoview as simple
   string transcriptions of the structure syntax. Of course, if we
   don't like this representation anymore, we're free to override the
   [Repr] class for [Point] by defining a new custom instance.

   But the point is that what Lean can automatically derive for us behaves
   sufficiently well for most purposes, saving the programmer a lot of
   time implmenting a few standard classes by hand - as we did above
   for the sake of explanation. -/

deriving instance BEq, Hashable for Pos -- Doesn't complain if already defined
deriving instance BEq, Hashable, Repr for NonEmptyList

-- # Appending

-- Homogeneous appending
@[default_instance]
instance : Append (NonEmptyList α) where
  append l1 l2 := { head := l1.head, tail := l1.tail ++ (l2.head :: l2.tail)}

-- https://spiderid.com/locations/united-states/idaho/?fwp_paged=3
#eval idahoSpiders ++ ⟨"Woodhouse Hunter",[]⟩ -- Uses the default instance

-- How does one overload list notation? Exercise

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys := ⟨xs.head, xs.tail ++ ys⟩ -- Relies on [HAppend]'s instance for [List]

#eval idahoSpiders ++ ["Woodhouse Hunter"]
#eval idahoSpiders ++ ([] : List String)

-- The other way around is a bit less obvious (official exercise, ~5 min)
instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend
  | [], ys => ys
  | x :: xs, ys => ⟨x,xs ++ ys.head :: ys.tail⟩

#eval ["Woodhouse Hunter", "Trapdoor Spider"] ++ idahoSpiders
#eval ([] : List String) ++ idahoSpiders


-- # Functors

#check @Functor
#check @Functor.map

/- A polymorphic type (such as [List α]) is a _functor_ if it overloads
   [Funtcor.map], a function that transforms every element contained in
   it by a function. -/

-- [List] already overloads [Functor.map], by [List.map]
#eval Functor.map (· + 5) [1, 2, 3]
#eval some (1 :: [2, 3])
#eval Functor.map toString (some (1 :: [2, 3]))
#eval Functor.map List.reverse [[1, 2, 3], [3, 2, 1]]

/- If a type can be transformed into another by [f], then a container for
   the first type can be transformed into a container for the second type.

   This is exactly what [map] does. Given a function [f : α → β] as argument,
   it returns a function on the containers such that [map f : F α → F b].

   [F] is the type constructor for the "container type",
   e.g. [F : Type → Type := fun τ → List τ] or simply [F := List]
-/

-- [<$>] is handy infix notation for [Functor.map]
#eval (· + 5) <$> [1, 2, 3]
#eval toString <$> (some (1 :: [2, 3]))
#eval List.reverse <$> [[1, 2, 3], [3, 2, 1]]

/- [Functor] wants the type container constructor, not an abstract
   application of it for some entry type α.
   That is to say, the type of the entries doesn't matter. -/
instance : Functor List where
  map := List.map

instance : Functor NonEmptyList where
  map f xs := ⟨f xs.head, List.map f xs.tail⟩

/- [NonEmptyList] is now a [Functor]
   (i.e., it is the [F] of the definition of functor -/
#eval ("Freaking cute " ++ ·) <$> idahoSpiders
#eval (· ++ " my beloved 🥹") <$> idahoSpiders
#eval ("✨💗✨" ++ · ++ "✨🕷️🕸️✨") <$> idahoSpiders

-- Making [PPoint] a functor is easy
instance : Functor PPoint where
  map f p := ⟨f p.x, f p.y⟩

def p2 := (· + 2) <$> p1
#eval (3.14 + ·) <$> p1

def atLeastOneFloatPoint : NonEmptyList (PPoint Float) := ⟨p1,[p2,p1,p2]⟩

#eval atLeastOneFloatPoint
-- Each application of [map] only goes down one layer
#eval ((· + 2) <$> ·) <$> atLeastOneFloatPoint

-- [List.concat] appends an entry at the end of a list
#check List.append
#check List.concat
#eval [1,2,3].concat 1
#eval [1,2,3].append [1]


/- A version of [concat] that reduces a [List α] to an [α]
   only makes sense on non-empty lists -/

-- First attempt, doesn't preserve order
def concatSilly [Append α] (xs : NonEmptyList α) : α :=
  let rec catTail : List α → α
  | [] => xs.head
  | y :: ys => y ++ catTail ys
  catTail xs.tail

#eval concatSilly idahoSpiders  -- puts the front element last, bad

-- Better version of book, also tail recursive
def NonEmptyList.concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
  | [] => start -- yield the accumulation
  | z :: zs => catList (start ++ z) zs
  catList xs.head xs.tail

/- Attempts at definition before peeking:
   Lean does not inspect the list field :(

  match xs.tail with
  | [] => xs.head
  | y :: ys => concat ⟨xs.head ++ y, ys⟩

  match xs.tail with
  | [] => xs.head
  | y :: ys => xs.head ++ concat ⟨y, ys⟩
-/

#eval idahoSpiders.concat -- relies on [String]s being [Append]able

#eval Functor.mapConst "1" [1,2,3]

/- Note that [Functor] also defines [mapConst] _default_ method for which
   it provides a definition that calls the user-defined [map].

   A _default_ method can be overridden, but the implementor is not
   required to implement it.

   In the case of [Functor], [mapConst] simply maps a constant function
   over the container.
-/

/- One might also write a buggy [Functor], i.e. an _unlawful_ functor.

   An unlawful constructor does more stuff than just mapping, such as
   moving around or erasing the elements of the list. -/
instance : Functor List where
  map _ _ := []

#eval (· + 5) <$> [1, 2, 3] -- erased the list!
#eval id <$> [1, 2, 3] -- mapping [id] should return the list untouched

def f (n : Nat) := toString n
def g := (· * 2)
def xs := [1, 2, 3]

#eval (fun y => f (g y)) <$> xs
#eval f <$> (g <$> xs)

/- (Aside) Lean has an operator for function composition, and
   [<$>] associates to the right! -/

#eval (f ∘ g) <$> xs
#eval f <$> (g <$> xs)

/- [LawfulFunctor] prevents buggy implementations by asserting
   that [map] preserves the identity and the composition laws.

   [LawfulFunctor] fires off a search for an instance of [Functor]
   for the given type constructor, plus it checks for a few theorems.

   The previous instance would be rejected, because evidence showing
   that the nonsensical [map] satisfies both [id_map] and [comp_map]
   cannot be crafted. -/
#check LawfulFunctor
#check LawfulFunctor.id_map
#check LawfulFunctor.comp_map

/- instance : LawfulFunctor NonEmptyList where
  id_map := by sorry
  comp_map := by sorry -/

def BinTree.map (f : α → β) : BinTree α → BinTree β
  | leaf => leaf
  | branch l a r => branch (l.map f) (f a) (r.map f)

instance : Functor BinTree where
  map := BinTree.map

def t1 := branch (branch leaf 2 leaf) 1 leaf
deriving instance Repr for BinTree

#eval (· + 5) <$> t1
#eval (·) <$> t1
#eval Functor.mapConst 3 t1
