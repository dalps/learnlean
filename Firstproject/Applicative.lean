#check LawfulApplicative

structure MythicalCreature where
  summon ::
  large : Bool
deriving Repr

#check MythicalCreature.summon

def medusa := MythicalCreature.summon false

-- ## Linear inheritance
#check MythicalCreature.large
#check MythicalCreature.large medusa

-- Every Monster is also a MythicalCreature
structure Monster extends MythicalCreature where
  spawn ::
  vulnerability : String
deriving Repr

#check Monster.spawn

def troll0 : Monster :=
  {large := false, vulnerability := "sunlight"}

def troll1 : Monster where
  large := false
  vulnerability := "sunlight"

/- A monster is created off of a mythical creature
   and arguments for each of its own fields -/
def troll2 : Monster := Monster.spawn ⟨false⟩ "sunlight"

#check Monster.toMythicalCreature

-- Extract the underlying creature
#eval troll0.toMythicalCreature

-- Anonymous angle-bracket notation reveals internal details, such as field order
def troll3 : Monster := ⟨false, "sunlight"⟩ -- Bad
def troll4 : Monster := ⟨⟨false⟩, "sunlight"⟩

-- Thanks to inheritance, dot notation works for supertype fields
#eval troll0.large -- Equivalent to [(troll0.toMythicalCreature).large]

/- The upcast is not performed automatically when the
   supertype method is applied outside of dot notation
   (a coercion from [Monster] to [MythicalCreater] is needed here) -/
#eval MythicalCreature.large troll0

instance : Coe Monster MythicalCreature where
  coe m := m.toMythicalCreature

-- Now it works!
#eval MythicalCreature.large troll0
#eval Monster.vulnerability troll0

-- Test if a creature is not large
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large

#eval troll0.small -- Lean inserts call to [toMythicalCreature]
#eval MythicalCreature.small troll0 -- Would throw type error if it wasn't for coercion

-- ## Multiple inheritance and automatic collapsing of diamonds
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"

structure MonstrousAssistant extends Monster, Helper where
deriving Repr

def benignTroll : MonstrousAssistant where
  large := true
  vulnerability := "sunlight"
  assistance := "plowing"
  payment := "toy goats"

/- The substructure inherits the common ancestor fields
   from the leftmost parent structure that it extends.
   This is how it solves diamond inheritance problem.
   Notice how the [mk] method includes only one parent
   structure argument, which is the one that was extended first,
   while the fields of subseqent extended structures are copied
   verbatim into the signature. -/
structure MonstrousAssistant' extends Helper, Monster where
deriving Repr

-- Notice the difference in arguments
#check MonstrousAssistant.mk
#check MonstrousAssistant'.mk

-- Both substructures reconstruct [Helper] and [Monster] in different ways:
#print MonstrousAssistant.toMonster
#print MonstrousAssistant.toHelper
#check MonstrousAssistant.toMythicalCreature -- Confused, [toHelper] calls it but I can't!?

#print MonstrousAssistant'.toMonster
#print MonstrousAssistant'.toHelper

-- ## Default implementations
inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large

#check SizedCreature

def mediumCreature : SizedCreature where
  size := Size.medium

-- Inconsistencies can still arise
def nonsenseCreature : SizedCreature where
  large := false
  size := .large

/- To be safe, users of [SizedCreature] must provide
   evidence of this proposition.
   Defined as [abbrev] so that [simp] can unfold its defitition.
-/
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)

def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by simp -- Don't understand why [simp] fails


/- Being encoded in structures, type classes also support inheritance and its features.
   A relevant example is the Monad - Functor hierarchy. -/

#print Monad
#print Applicative
#print Functor

/- Indeed, [Monad] inherits the [pure] method from [Applicative].
   [seq] is a stands in the middle of [Monad]'s [bind] and [Functor]'s [map].

   While [Functor.map] applies a function _unconditionally_ to the
   contents of a datatype, [seq] controls how the function is applied
   by having it under the container type [f].
-/

#check Applicative.toSeq
#check Seq.seq

instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with -- Is there a function to be applied?
    | none => none
    | some g => g <$> x () -- Remember the convenience of [Functor]: apply a function over the contents of a container directly to the container

instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x := do
    let g ← f
    g <$> x ()

/- The [Unit] parameter allows to short-circuit the definition of [seq]
   in cases where the function will never be applied. This way the
   surrounding structure decides when to short-circuit the evaluation of the argument, rather than the function itself.

   Thanks to [seq], [Monads] can guarantee execution order,
   as informed by [Applicative]. [Applicative] also takes care of
   applying a function in a context with side effects.

   So, what exactly does [Monad] add that [Applicative] doesn't have?
-/

#check some Add.add
#check some Add.add <*> some 4
#check some Add.add <*> (none : Option Nat)
#check some Add.add <*> some 4 <*> some 7
#check some Add.add <*> none <*> some 7

/- [Pair] is a container, however it is not applicative: it does not
   allow the sequencing of operations...
-/
structure Pair (α β : Type) : Type where
  first : α
  second : β
deriving Repr

instance : Functor (Pair α) where
  map f p := ⟨p.first, f p.second⟩

#check Functor.map
#eval (· * 2) <$> ({first := 1, second := 2} : Pair Nat Nat)

#check LawfulFunctor

/- [Pair α] obeys the [Functor] contract:

  1. [id] is a left identity of [<$>] ("dollar diamond")
  id <$> x = x
  ===>
  map id x
  ===>
  ⟨x.first, id x.second⟩
  ===>
  ⟨x.first, x.second⟩
  ===>
  x

  2. Composition law: composing [h] and [g] before or after [<$>] doesn't matter
  (h ∘ g) <$> x
  ===>
  map (h ∘ g) x
  ===>
  ⟨x.first, (h ∘ g) x.second⟩
  ===>
  ⟨x.first, h (g x.second)⟩

  h <$> g <$> x
  ===>
  map h (map g x)
  ===>
  map h ⟨x.first, g x.second⟩
  ===>
  ⟨⟨x.first, g x.second⟩.first, h ⟨x.first, g x.second⟩.second⟩
  ===>
  ⟨x.first, h (g x.second)⟩
-/

-- ...let alone terminating a sequence of [Pair]s
def Pair.pure (x : β) : Pair α β := Pair.mk _ x -- No [α] available

/-
  instance : Applicative (Pair α) where
  pure (x : β) := _

  Going off intuition, product types are never applicative functors.
  [pure] needs to work for _all possible types_ of the first component,
  including [Empty]. But this means that there might not be a product value available for [pure], because [α] may have no values at all.
-/


/- Is [List] an applicative functor? Yes. It is also a monad. -/
instance : Functor List where
  map := List.map

#check List.bind
#print List.bind
#check List.join

instance : Monad List where
  pure := List.pure
  bind := List.bind -- So cool, it works in parallel for each single element

#eval [1,2,3,4,5].bind List.range

def List.seq {α β : Type} (fs : List (α → β)) (xs : Unit → List α) : List β := do
  let x ← xs () -- For every element
  let f ← fs    -- For every function
  pure (f x)    -- Apply the function to the element

def List.seqSilly {α β : Type} (fs : List (α → β)) (xs : Unit → List α) :=
  match fs, xs () with
  | g :: gs, y :: ys => g y :: gs.seqSilly (fun () => ys)
  | _, _ => nil
-- Omg, spent a good 30 mins not realizing I was calling [seq] here...

instance : Applicative List where
  pure x := [x]
  seq := List.seq

#eval [(· + 3), (· * 2), (-·)] <*> [3,3,-6]
#eval [(· + 3), (· * 2), (-·)] <*> [1000,100,10,1,-1,-10,-100,-1000]
#eval [(· + 3), (· * 2), (-·)] <*> [1000,100,10,1,-1,-10,-100,-1000] |> List.length
