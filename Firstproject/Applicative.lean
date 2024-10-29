import Firstproject.NonEmptyList
import Firstproject.Many

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

-- # The Validate applicative functor

/- Let's combine the [Expect ε] monad with the [WithLog logged] monad
  to validate user input. This combination won't be a new monad though,
  rather an applicative functor.

  Much like [Except], [Validate] allows to characterize whether the collected data is valid or not. Unlike [Except] it allows to keep track of _multiple errors_ that may be present in the data, gathered
  in a list in a similar function to [WithLog].
-/

structure RawInput where
  name : String
  birthYear : String

/- A [Subtype] is a [Type] equipped with a predicate over its values.
   It characterizes the values of [α] that satisfy [p], therefore a
   _subset_ of [α]. The subtype enjoys the property [p], one could say.
-/
structure Subtype' {α : Type} (p : α → Prop) where
  val : α
  property : p val

/- Lean has special notation - reminiscent of Coq's - for subtypes.

  For example, one can define a subtype of [Nat] that rules
  out zero. We already did encoded positive numbers with [PosNat], but the advantage of this method is in the special treatment of the [Nat] and [Int] types. Lean implements these primitive types with heavy optimizations, something that user-defined inductive types don't get to enjoy.

  Thus, [FastPos] is faster than [PosNat].
-/
def FastPos : Type := {x : Nat // x > 0}

/- In order to build a [FastPos], you need to supply a structure containing a [Nat] and evidence that it is less than zero.
-/
example : FastPos := ⟨1, by simp⟩

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp_arith⟩

example : FastPos := 1

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  /- You can name the assumption of an [if]'s guard.
     It's a proposition, after all.
     It is necessary to do so for building a [FastNat] from a [Nat].

     [h] is bound to some evidence in both branches,
     check it out in the Infoview.
  -/
  if h : n > 0 then
    some ⟨n, h⟩
  else none

/- Let's implement the business logic of the validator.
  The [CheckedInput] characterizes sanitized data. It is parameterized on the year that validation is performed, and it relies on subtypes.

  The individual checks to be performed are conjucts in the subtypes' properties.

  The contraints are:
  * The name may not be empty
  * The birth year must be numeric and non-negative
  * The birth year must be greater than 1900 and less than or equal to the year in which validation is performed
-/
structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {n : Nat // n > 1900 /\ n ≤ thisYear}

/- The input validator is an applicative functor.
   The only difference that sets it apart from [Except] is that [Validate] is able to carry multiple failures, as documented by the [NonEmptyList] argument.
-/

inductive Validate (ε α : Type) : Type where
  | errors : NonEmptyList ε → Validate ε α
  | ok : α → Validate ε α

-- Redefined for the sake of example
instance : Functor (Except ε) where
  map f
    | .ok a => .ok $ f a
    | .error e => .error e

#eval (· + 1) <$> (.ok 2 : Except String Nat)

-- First and foremost, [Validate] is a functor.
instance : Functor (Validate ε) where
  map f
    | .ok a => .ok $ f a
    | .errors errs => .errors errs

#check Seq.seq
#eval .ok (· + 1) <*> (.ok 2 : Except String Nat)
#eval .ok (· + 1) <*> (.error "bad value" : Except String Nat)
#eval .ok (· + 1 + ·) <*> (.error "bad value" : Except String Nat) <*> .ok 1
/-
  #eval
  ((Except.ok (· + 1) <*> fun () =>
  Except.ok 2) : Except String Nat)
 -/

#check LawfulApplicative.seq_assoc
/- While [Functor] only transforms _successful_ values
  of the container, [Applicative] may also operate
  on the faulty values and behave accordingly
with respect to them. -/

-- Got it right - ~10 min
instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .errors errsSoFar =>
      match x () with
      | .errors errsNow => .errors (errsSoFar ++ errsNow)
      | .ok _ => .errors errsSoFar
    | .ok nextCheck =>
       nextCheck <$> x ()

def Field := String

def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors [(f, msg)]

/- The [Applicative] instance for [Validate] allows the checking
  procedures to be applied independently to the fields and then composed.
  Let's defined checking the procedures separately, and
  sequence them later.
-/
def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

/- Some checks makes sense only if performed on data
  that has been filtered by previous checks.
  [Validate.andThen] forces an order upon checks.

  Notice that this definition doesn't mention an instance of [Happend].
  Indeed, it makes sense not to accumulate errors when an order is
  imposed on checks: the only error, if any, will come from the first check in the sequence that fails, the other checks won't be executed
  because the sequence short-circuits.
-/
def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok filtered => next filtered

/- ~10 min
  Using [Validate.andThen] as [bind] for a [Monad (Validate ε)]
  instance will create a default [seq] that behaves very
  differently from our custom [seq]! In particular,
  the generated [seq] won't accumulate errors in an appendable
  structure because [andThen] never mentions [++]. -/

/- Is this a suitable [bind] for the [Monad] contract?
   Yes, on its own [andThen] satisfies the monad contract. However,
   for the reason stated above, it is not safe to implement a [Monad]
   instance of [Validate].
-/
namespace IfValidateWereAMonad
  instance : Monad (Validate ε) where
    pure := Validate.ok
    bind := Validate.andThen

  -- Let's see how the new [seq] fares against a couple of errors
  def notFun : Validate String (Nat → String) :=
    .errors ["First error"]

  def notArg : Validate String Nat :=
    .errors ["Second error"]

  deriving instance Repr for Validate
  #eval notFun <*> notArg -- Using [Applicative (Validate String)]'s [<*>] reports both errors

  #eval Seq.seq notFun (fun () => notArg) -- Uses the same definition

  /-
    notFun <*> notArg
    ===>
    match notFun with
    | .ok f => f <$> notArg
    | .errors errs =>
      match notArg with
      | .ok _ => .errors errs
      | .errors moreErrs => .errors (errs ++ moreErrs)
    ===>
    match .errors ["First error"] with
    | .ok f => f <$> notArg
    | .errors errs =>
      match .errors ["Second error"] with
      | .ok _ => .errors errs
      | .errors moreErrs => .errors (errs ++ moreErrs)
    ===>
    .errors (["First error"] ++ ["Second error"])
    ===>
    .errors ["First error", "Second error"]
  -/

  /- Replacing the definition of [seq] generated by the monad
     instance yields just one error: -/
  #eval notFun >>= fun f =>
        notArg >>= fun x =>
        pure (f x)

  /-
    seq notFun (fun () => notArg)
    ===>
    notFun >>= fun g =>
    notArg >>= fun y =>
    pure (g y)
    ===>
    match notFun with
    | .errors errs => .errors errs
    | .ok f => (fun g =>
                notArg >>= fun y =>
                pure (g y)) f
    ===>
    match notFun with
    | .errors errs => .errors errs
    | .ok f => notArg >>= fun y =>
               pure (f y)
    ===>
    match notFun with
    | .errors errs => .errors errs
    | .ok f => match notArg with
               | .errors errs' => .errors errs'
               | .ok x => (fun y => pure (f y)) x
    ===>
    match notFun with
    | .errors errs => .errors errs
    | .ok f => match notArg with
               | .errors errs' => .errors errs'
               | .ok x => .ok (f x)
    ===>
    match .errors ["First error"] with
    | .errors errs => .errors errs
    | .ok f => match .errors ["Second error"] with
               | .errors errs' => .errors errs'
               | .ok x => .ok (f x)
    ===>
    .errors ["First error"]
  -/
end IfValidateWereAMonad

def checkYearIsNat (year : String) : Validate (Field × String) Nat := -- Not a subtype, yet
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some y => pure y

def checkBirthYear (thisYear year : Nat) : Validate (Field × String) {x : Nat // x > 1900 /\ x <= thisYear} :=
  if gt1900 : year > 1900 then
    if ltThisYear : year <= thisYear then
      pure ⟨year, And.intro gt1900 ltThisYear⟩ -- [ /\ ] combines [Prop]s, not evidences
    else
      reportError "birth year" s!"Must be earlier than {thisYear}"
  else
    reportError "birth year" "Must be born after 1900"

-- Finally, we assemble our validator using [seq]:
def checkInput (year : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
  checkName input.name <*>
  (checkYearIsNat input.birthYear).andThen fun y =>
  checkBirthYear year y

/- I get it now: [<*>] feeds arguments to a function that awaits inputs,
  with the additional power of deviating if error occurs in the argument,
  or handling side effects in general. -/
example : Except String Nat := Except.pure (· * · + · - ·) <*> .ok 3 <*> .ok 2 <*> .ok 1 <*> .ok 0

deriving instance Repr for CheckedInput
deriving instance Repr for Validate
#eval checkInput 2024 $ RawInput.mk "Vladimir" "1923"
#eval checkInput 2024 $ RawInput.mk "" "1923"
#eval checkInput 2024 $ RawInput.mk "Vladimir" "1900"
#eval checkInput 2024 $ RawInput.mk "Vladimir" "2029"
#eval checkInput 2024 $ RawInput.mk "Vladimir" "syszyg"
#eval checkInput 2024 $ RawInput.mk "" "syszyg"
#eval checkInput 2024 $ RawInput.mk "" "1492" -- "Runs the rest of the checks in spite of errors!"

/- What [Applicative] brings to the table:
   * Keep running the program in spite of errors, because the
     diagnostic data reveals important information nevertheless
   * Parallel execution
-/

-- # The Applicative Contract

#check Seq.seq
#check LawfulApplicative
#check Functor.map

-- An applicative functor must:

-- 1. Respect identity:
#eval some id <*> some 3

-- 2. Respect function composition:
#eval some (· ∘ ·) <*>
  some (· * 2) <*>
  some (· + 1) <*>
  some 3

#eval some (· * 2) <*> (some (· + 1) <*> some 3)

#eval some ((· * 2) ∘ (· + 1)) <*> some 3

#eval some ((· == 4) ∘ (· + 1)) <*> some 3

-- 3. Sequencing pure operations shouldn't produce side-effects
#eval some (3 - ·) <*> some 3
#eval (3 - ·) 3

-- 4. The order of pure operations doesn't matter
#eval (none : Option (Float → Float)) <*> some 3.14
#eval some (· 3.14) <*> (none : Option (Float → Float))

/- Let's show each of these for the [Applicative Option] instance:
  For this instance, [pure] is simply [Option.some].
  Recall the definition of [seq] for the [Option] instance:

  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()

  In the following proofs, the application of [()] is implicit
  for the sake of brevity.

  1.
  pure id <*> v = v
  ===>
  some id <*> v = v
  ===>
  id <$> v

  If [v = none], then by definition of [<$>] for the [Option]
  instance, [id <$> v] is also [none].

  Otherwise [v = some x] for some [x], then:

  id <$> some x ===> some (id x) ===> some x

  Which is equal to [v].

  2.
  some (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)

  If any of [u], [v], [w] is [none], then both sides are
  trivially [none] by definition of [seq] and [<$>].

  Assume [u = some g], [v = some f], [w = some x], for any
  functions [f] and [g] and any value [x].

  We reduce both sides separately and show that they reduce
  to the same value.

  some (· ∘ ·) <*> some g <*> some f <*> some x
  ===>
  (· ∘ ·) <$> some g <*> some f <*> some x
  ===>
  some (g ∘ ·) <*> some f <*> some x
  ===>
  (g ∘ ·) <$> some f <*> some x
  ===>
  some (g ∘ f) <*> some x
  ===>
  (g ∘ f) <$> some x
  ===>
  some ((g ∘ f) x)
  ===>
  some (g (f x))

  some g <*> (some f <*> some x)
  ===>
  some g <*> (f <$> some x)
  ===>
  some g <*> some (f x)
  ===>
  g <$> some (f x)
  ===>
  some (g (f x))

  3.
  some f <*> some x = some (f x)

  some f <*> some x
  ===>
  f <$> some x
  ===>
  some (f x)

  4.
  u <*> some y = some (· y) <*> u

  If [u = none], both sides reduce to [none]:

  none <*> some y ===> none
  some (· y) <*> none ===> (· y) <$> none ===> none

  If [u = some f] for any [f], then both sides reduce to [some (f y)]:

  some f <*> some y ===> f <$> some y ===> some (f y)

  some (· y) <*> some f ===> (· y) <$> some f
  ===> some ((· y) f) ===> some (f y)

  Qed.
-/

#check LawfulApplicative

/- All Applicatives are Functors: [Functor.map] can be redefined
   solely in terms of [Applicative.seq] and [Applicative.pure].
-/

def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x

/- [Functor.map] fails only if [x] does.
   This motivates the need to inspect variables when they
   are on the left [<$>] in the above proofs.

   [Functor] can be implemented from [Applicative] provided that
   the [Applicative] contract implies (_is more powerful_) than
   the [Functor] contract.

   Recall the [Functor] contract:

   1. It preserves the identity: (immediate)

      id <$> x = x.

      This follows directly from the first rule of [Applicative].

      id <$> x = x ===> pure id <*> x ===> x

   2. Mapping the composition of two functions is the same as
      mapping them separately but in the same order:
      (~10 min)

      (h · g) <$> x = h <$> g <$> x

      This follows from the second rule rule:
      (wasted ~10 min by starting from left...)

      h <$> g <$> x
      ===>
      pure h <*> (g <$> x)
      ===>
      pure h <*> (pure g <*> x)
      =     By 2rd rule
      pure (· ∘ ·) <*> pure h <*> pure g <*> x
      =     By 3rd rule (x2)
      pure (h · g) <*> x
-/

class Applicative' (f : Type → Type) extends Functor f where
  pure : α → f α
  seq : f (α → β) → (Unit → f α) → f β
  map f x  := seq (pure f) (fun () => x)

/- All Monads are Applicative functors: [Monad] already has
  [pure] (actually, it inherits it from [Applicative]), and
  [bind] suffices for defining [seq] -/
def seq [Monad m] (mf : m (α → β)) (mx : Unit → m α) : m β := do
  let f ← mf
  let x ← mx ()
  pure (f x)

/- If the [Monad] contract implies the [Applicative] contract,
   then we can use the above [seq] as a default definition of
   the omonymous filed if [Monad] extends [Applicative].

    Indeed, it does.

    In the following proof, if is safe to omit [()] for brevity.

    1. - ~12 min
    pure id <*> x
    ===>
    pure id >>= fun g =>
    x () >>= fun y =>
    pure (g y)
    ={ By the 1st rule of monads }=>
    (fun g => x () >>= fun y => pure (g y)) id
    ===>
    x () >>= fun y => pure (id y)
    ===>
    x () >>= fun y => pure y
    ===>
    x () >>= pure
    ={ By the 2nd rule }=>
    x ()

    2. +3:30 hours
    pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)

    Proceed reducing both sides separately.
    Remember:
    * [<*>] is left associative.
    * Abstractions' bodies extend as far down/right as possible

    u <*> (v <*> w) -- Assume [u : m (α → β)] and [v <*> w : m α]
    ===>
    u >>= fun f =>
    (v <*> w) >>= fun gy =>
    pure (f gy)
    ===>
    u >>= fun f =>
    ( v >>= fun g =>
      w >>= fun y =>
      pure (g y) ) >>= fun gy =>
    pure (f gy)
    ={ association (←) }=>
    u >>= fun f =>
    v >>= fun g =>
    w >>= fun y =>
    pure (g y) >>= fun gy =>
    pure (f gy)
    ={ first rule }=>
    u >>= fun f =>
    v >>= fun g =>
    w >>= fun y =>
    (fun gy => pure (f gy)) (g y)
    ={ simplify }=>
    u >>= fun f =>
    v >>= fun g =>
    w >>= fun y =>
    pure (f (g y))

    Is equal to:

    pure (· ∘ ·) <*> u <*> v <*> w
    ===>
    ((pure (· ∘ ·) <*> u) <*> v) <*> w
    ===>
    seq (seq (seq (pure (· ∘ ·)) u) v) w
    ===>
    ((pure (· ∘ ·) >>= fun comp =>
        u >>= fun f =>
       pure (comp u)) >>= fun thenF =>
      v >>= fun g =>
     pure (thenF g)) >>= fun gThenF =>
    w >>= fun x =>
    pure (gThenF x)
    ={ apply left identity }=>
    ((fun comp =>
        u >>= fun f =>
       pure (comp f)) (· ∘ ·) >>= fun thenF =>
      v >>= fun g =>
     pure (thenF g)) >>= fun gThenF =>
    w >>= fun x =>
    pure (gThenF x)
    ={ simplify }=>
    ((u >>= fun f =>
       pure ((· ∘ ·) f)) >>= fun thenF =>
      v >>= fun g =>
     pure (thenF g)) >>= fun gThenF =>
    w >>= fun x =>
    pure (gThenF x)
    ={ simplify }=>
    ((u >>= fun f =>
        pure (f ∘ ·)) >>= fun thenF =>
       v >>= fun g =>
      pure (thenF g)) >>= fun gThenF =>
     w >>= fun x =>
    pure (gThenF x)
    ={ insert parentheses }=>
    ((u >>= fun f =>
        pure (f ∘ ·)) >>= (fun thenF =>
       v >>= fun g =>
      pure (thenF g))) >>= fun gThenF =>
     w >>= fun x =>
    pure (gThenF x)
    ={ I'm lost }=> -- How do I apply associativity here?! Nothing matches the RHS of the rule! ~1h30min
    (u >>= fun f =>
     pure (f ∘ ·) >>= fun thenF =>
     v >>= fun g => pure (thenF g)) >>= fun gThenF =>
     w >>= fun x =>
     pure (gThenF x)
    ={ 1st rule }=>
    (u >>= fun f =>
      (fun thenF => v >>= fun g => pure (thenF g)) (f ∘ ·)
    ) >>= fun gThenF =>
    w >>= fun x =>
    pure (gThenF x)
    ={ simplify }=>
    (u >>= fun f =>
     v >>= fun g => pure ((f ∘ ·) g)) >>= fun gThenF =>
    w >>= fun x =>
    pure (gThenF x)
    ={ simplify }=>
    (u >>= fun f =>
     v >>= fun g => pure (f ∘ g)) >>= fun gThenF =>
    w >>= fun x =>
    pure (gThenF x)
    ={ associativity (definitely not 3rd rule) }=>
    u >>= fun f =>
    v >>= fun g =>
    pure (f ∘ g) >>= fun gThenF =>
    w >>= fun x =>
    pure (gThenF x)
    ={ 1st rule }=>
    u >>= fun f =>
    v >>= fun g =>
    (fun gThenF =>
    w >>= fun x =>
    pure (gThenF x)) (f ∘ g)
    ={ simplify }=>
    u >>= fun f =>
    v >>= fun g =>
    w >>= fun x =>
    pure ((f ∘ g) x))
    ={ simplify }=>
    u >>= fun f =>
    v >>= fun g =>
    w >>= fun x =>
    pure (f (g x))
    ={ Lemma 1 }=>
    u >>= fun f =>
    v >>= fun g =>
    w >>= fun x =>
    pure (g x) >>= fun q =>
    pure (f q)
    ={ associativity }=>
    u >>= fun f =>
    v >>= fun g =>
    (w >>= fun x =>
    pure (g x)) >>= fun q =>
    pure (f q)
    ={ associativity }=>
    u >>= fun f =>
    ( v >>= fun g =>
    ( w >>= fun x =>
      pure (g x) ) ) >>= fun q =>
    pure (f q)
    ={ associativity }=>
    u >>= fun f =>
    ( v >>= fun g =>
      w >>= fun x =>
      pure (g x) ) >>= fun q =>
    pure (f q)
    ={ definition of [seq] }=>
    u >>= fun f =>
    ( seq v w ) >>= fun q =>
    pure (f q)
    ={ definition of [seq] }=>
    seq u ( seq v w )
    ={ to be precise... }=>
    seq u ( fun () => seq v ( fun () => w ) )

  Lemma 1:
  pure x >>= fun q => pure (f q) = pure (f x)

  pure x >>= fun q => pure (f q)
  ={ [pure] is a left identity of [>>=] }=>
  (fun q => pure (f q)) x
  ={ simplify }=>
  pure (f x)

  Note: [fun q => pure (f q)] and [f] are *not* the
  same thing! Their types are different!

  Lemma 2:
           w >>= fun z =>
  pure (y z) >>= fun q =>
  pure (x q)
  =
  (w >>= fun z => pure (y z)) >>= fun q =>
  pure (x q)

  w >>= fun z =>
  pure (y z) >>= fun q =>
  pure (x q)
  ={ insertion of parentheses }=>
  w >>= ( fun z =>
  pure (y z) >>= (fun q =>
  pure (x q)) )
  ={ associativity [f = fun z => pure (y z)] }=>
  ( w >>= fun z =>
  pure (y z) ) >>= (fun q =>
  pure (x q))
  ={ remove parentheses }=>
  (w >>= fun z => pure (y z)) >>= fun q =>
  pure (x q)

  [>>=] is left-associative!!!
  https://github.com/leanprover/lean4/blob/01d414ac36dc28f3e424dabd36d818873fea655c/src/Init/Notation.lean#L346-L346

  x >>= f >>= g  =  (x >>= f) >>= g

  The lower precedence of abstractions tricked me into thinking it was right-associative.
  And you can take the [f x] of the definition to be
  just about anything happens to be on the right of [>>=].

    3. 6:44 min
    pure f <*> pure x = pure (f x)

    seq (pure f) (fun () => pure x)
    ={ definition of seq }=>
    pure f >>= fun g =>
    pure x >>= fun y =>
    pure (g y)
    ={ left identity }=>
    pure x >>= fun y =>
    pure (f y)
    ={ left identity }=>
    pure (f x)

    4. 10:56 min - Contrary to author, I started from the right member
    u <*> pure y = pure (fun f => f y) <*> u

    seq (pure (fun f => f y)) (fun () => u)
    ={ definition of seq }=>
    (pure (fun f => f y)) >>= fun g =>
    u >>= fun v =>
    pure (g v)
    ={ left identity }=>
    u >>= fun v =>
    pure ((fun f => f y) v)
    ={ simplify }=>
    u >>= fun v =>
    pure (v y)
    ={ Lemma 1 (←) }=>
    u >>= fun v =>
    pure y >>= fun z =>
    pure (v z)
    ={ definition of seq }=>
    seq u (fun () => pure y)
    ==>
    u <*> pure y
-/

/-
    Bad attempt
    ={ Moving backwards: 1st rule ← }=>
    u >>= fun f =>
    v >>= fun g =>
    w >>= fun x =>
    pure (pure (g x) >>= f)
    ={ Moving backwards: 1st rule ← }=>
    u >>= fun f =>
    v >>= fun g =>
    w >>= fun x =>
    pure (pure (pure x >>= g) >>= f)

    Rewriting → doesn't make progress
    u >>= (fun z => (fun f =>
    ( v >>= fun g =>
      w >>= fun y =>
      pure (g y) ) ) z >>= fun gy => pure (f gy))


    Recall the association law of the monad contract:

    x >>= f >>= g  =  x >>= (fun y => f y >>= g)

    Which can also be writted without parentheses:

    x >>= f >>= g  =  x >>= fun y => f y >>= g

    It basically allows you to "slice" the body of
    an abstraction until [g] the next [>>=] and use
    it as the second operator of the first [>>=].

    Another way to digest it: it doesn't matter
    whether you first reduce [f >>= g] in a context
    where [x] is taken abstract or you first reduce [x],
    use it to compute [f] and then [g], the result is the same.
-/

#check LawfulMonad
#check LawfulApplicative
#check LawfulFunctor
#check Seq.seq

/- This proof justify a definition of [Monad] that
   extends [Applicative]. The [pure] and [bind] suffice
   to give a default definition of [seq] (~5 min) -/
class Monad' (m : Type → Type) extends Applicative m where
  bind : m α → (α → m β) → m β
  seq f x :=
    bind f      fun g =>
    bind (x ()) fun y =>
    pure (g y)
  /- The instance of [Applicative] already takes care
     of defining [map] by means of [seq], yet it is
     instructive to see its relationship with [bind]. -/
  map f x :=
    -- seq (pure f) (fun () => x)
    bind (pure f) fun g =>
    bind x        fun y =>
    pure (g y)

-- # Alternatives

abbrev NonEmptyString := {s : String // s ≠ ""}

/- There are two alternative validations paths now:
   Input may be valid for different reasons and
   a correct validator should address all variants.

   This is equivalent to defining multiple [CheckedInput]
   structures to characterize distinct sets of valid input.
-/
inductive LegacyCheckedInput
  | humanBefore1970 : -- You can have named parameters after :
    (birthYear : {y : Nat // y > 999 /\ y < 1970}) → -- YoB is a number, and must be no later than 1969
    String → -- Name not required, can be in fact empty
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970 /\ y < 10000}) →
    NonEmptyString → -- Name required
    LegacyCheckedInput
  | company :
    /- (birthYear : {s : NonEmptyString // s = "FIRM"}) → NO, input is fixed. It would be wasteful and useless to carry around
    the string "FIRM". The constructor itself guarantees the name
    field was filled with "FIRM" exactly, otherwise the
    validator would have failed or produced another one. -/
    NonEmptyString →
    LegacyCheckedInput
deriving Repr

/- The new validator is able to recover from failures and move on
   to the remaining cases, while preserving error messages.

   To this purpose we introduce the [orElse] operator.

   Notice the difference with [andThen]'s signature:
   1. The lazy parameter: no need to look into other cases
     (and therefore spend resources) if the current case succeeds.
   2. Both cases have the same result type.
   3. Branching rather than sequencing.

   ~5 min
-/
def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok a => .ok a
  | .errors aErrs =>
    match b () with
    | .ok b => .ok b -- Recover from failure
    | .errors bErrs => .errors (aErrs ++ bErrs) -- Preserve errors

/-
  Lean supports this pattern with two dedicated type classes.

  The homogenous [OrElse] allows to recover from the failures
  in the first argument by evaluating the second one, which must
  have the same type.

  class OrElse (α : Type) where
    orElse : α → (Unit → α) → α

  [OrElse.orElse] is bound to the infix operator [<|>], too.
-/
instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

/-
  To build a global validator for [LegacyCheckedInput], we build
  validators for each constructor and combine then with [<|>].

  The local checks of the constructor are sequenced with [<*>]
  as we saw before.

  The [company] constructor is peculiar in that it is implied by anonymous evidence that the name field of the form matches "FIRM".
  The evidence can be anonymous because it won't be recorded: this
  is implemented with a throwaway [Unit] and a function that
  ignores its argument.
-/
def checkThat (condition : Bool) (field : Field) (msg : String) :
  Validate (Field × String) Unit :=
  if condition then
    .ok ()
  else
    reportError field msg

/- Validators for different cases may share the same logic for common fields!
   Here we reuse the [checkName] routine. ~10 min
-/
def checkCompany'' (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  pure (fun _ => LegacyCheckedInput.company) <*>
  checkThat (input.birthYear == "FIRM") "birth year" "Not a company" <*>
  checkName input.name

-- Without the noise

#check Seq.seq
#check SeqRight.seqRight

-- Whatever you want ignore, have it _to the right_ of [*>]
def checkCompany' (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "Not a company" *>
  pure LegacyCheckedInput.company <*> checkName input.name

-- [*>] is a specialization of [<*>] - ~5 min, peeked
def seqRight [Applicative f] (a : f α) (b : Unit → f β) : f β :=
  pure (fun _ x => x) <*> a <*> b ()

/- Can be simplified further if you recall that for [Applicative]
   [f <$> x = pure f <*> x] holds. Using [pure] with a function you want
   to apply anyway is overkill. -/
def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "Not a company" *>
  .company <$> checkName input.name

-- Helper to check subtype fields - ~7 min
def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  -- If you want to test a [Prop], it must be [Decidable]
  if h : p v then
    .ok ⟨v,h⟩
  else
    .errors [err]

-- ~25 min (peeked)
def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
  .humanBefore1970 <$>
  checkSubtype y (fun y => y > 999 /\ y < 1970) ("birth year", "Born in or after 1970") <*>
  pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
  .humanAfter1970 <$>
  checkSubtype y (fun y => y > 1970 /\ y < 10000) ("birth year", "Born before 1970") <*>
  checkSubtype input.name (fun s => s ≠ "") ("name", "Required")

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|>
  checkHumanAfter1970 input <|>
  checkHumanBefore1970 input

#eval checkLegacyInput {name := "Joe", birthYear := "1972"}
#eval checkLegacyInput {name := "", birthYear := "1972"}
#eval checkLegacyInput {name := "Joe", birthYear := "1969"}
#eval checkLegacyInput {name := "", birthYear := "1969"}
#eval checkLegacyInput {name := "", birthYear := "FIRM"}
#eval checkLegacyInput {name := "ACME", birthYear := "FIRM"}
#eval checkLegacyInput {name := "ACME", birthYear := "999"}
#eval checkLegacyInput {name := "", birthYear := "1970"}
-- TODO: get [NonEmptyList.toString] to work here!

-- Introducing Alternative Applicative Functors:
instance : Alternative Option where
  failure := none
  orElse -- Returns the first [some] available
    | none, b => b ()
    | some a, _ => .some a

def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, bs => bs ()
  | .more a as, bs => more a (fun () => orElse (as ()) bs)
  -- fun () => (as ()).union (bs ()) -- Should be the same thing, right?

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse

/- [Alternative] allows to define interesting operations for
   [Applicative]. An example is [guard], which fails the
   program if a decidable proposition is false, otherwise
   it does nothing.

   Useful in monadic programs to terminate execution early,
   much like throwing an exception.
-/
def guard' [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then
    pure ()
  else failure

/- For [Many], it can be used to filter out a branch of a
   search. Recall [Many] is a [Monad], and therefore also an
   [Applicative]. -/
def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => Many.countdown n)

#eval Many.countdown 3

/-
evenDivisors 12 = [6,4,2]
evenDivisors 13 = []
evenDivisors 14 = [2]
evenDivisors 16 = [8,4,2]

11, 10, 9, 8, 7, ..., 0

~17:53 min - Errors:
  - Doesn't include [n] itself
  - Sequencing two guards is preferable to conjunction
-/

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1) -- A number in [0,n)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k

#eval evenDivisors 9
#eval evenDivisors 12
#eval evenDivisors 18
#eval evenDivisors 20
#eval evenDivisors 5040

namespace ImproveValidate

inductive Validate (ε α : Type) : Type where
  | errors : ε → Validate ε α
  | ok : α → Validate ε α

instance : Functor (Validate ε) where
  map f
  | .ok a => .ok $ f a
  | .errors errs => .errors errs

/- You can't define this outside and reuse it for both the
   original implementation and the exercise, it breaks some
   typing assumptions.
-/
def Validate.seq [Append ε] (f : Validate ε (α → β)) (x : Unit → Validate ε α) : Validate ε β :=
  match f with
    | .errors errsSoFar =>
      match x () with
      | .errors errsNow => .errors (errsSoFar ++ errsNow)
      | .ok _ => .errors errsSoFar
    | .ok nextCheck =>
       nextCheck <$> x ()

instance [Append ε] : Applicative (Validate ε) where
  pure := .ok
  seq := Validate.seq

instance [Append ε] : OrElse (Validate ε α) where
  orElse
  | .ok a, _ => .ok a
  | .errors errs, b =>
    match b () with
    | .errors moreErrs => .errors (errs ++ moreErrs)
    | .ok b => .ok b
-- ~20 min

def Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α
  | .ok a, _ => .ok a
  | .errors errs, f => .errors (f errs)

/-
  instance : Alternative (Validate ε) where
    failure := Validate.errors -- Impossible
-/
deriving instance Repr for Field

inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := TreeError.both

def reportError (field : Field) (msg : String) : Validate TreeError α :=
  .errors (TreeError.field field msg)

/- The legacy validation system, written with [TreeError]
   instead of [NonEmptyList] for user-friendlier reports. -/

#check guard
#check checkThat

-- The equivalent of [guard]
def checkThat (condition : Bool) (field : Field) (msg : String) : Validate TreeError Unit :=
  if condition then
    pure ()
  else
    reportError field msg

def checkName (name : String) : Validate TreeError {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else
    .ok ⟨name,h⟩

def checkYearIsNat (year : String) : Validate TreeError Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some y => pure y

def checkCompany (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "Not a company" *>
  LegacyCheckedInput.company <$> checkName input.name

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .ok filtered => next filtered
  | .errors errs => .errors errs

def checkSubtype {α : Type} (v : α) (p : α → Prop)
  [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    .ok ⟨v,h⟩
  else
    .errors err

def checkHumanAfter1970 (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
  LegacyCheckedInput.humanAfter1970 <$>
  checkSubtype y (fun y => y > 1970 /\  y < 10000) (.field "birth year" "Born before 1970") <*>
  checkSubtype input.name (fun s => s ≠ "") (.field "name" "Required")

def checkHumanBefore1970 (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
  LegacyCheckedInput.humanBefore1970 <$>
  checkSubtype y (fun y => y > 999 /\ y < 1970) (.field "birth year" "Born in or after 1970") <*>
  pure input.name

def checkLegacyInput (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  (checkCompany input).mapErrors (.path "Company user") <|>
  (checkHumanAfter1970 input).mapErrors (.path "Born after 1970 user") <|>
  (checkHumanBefore1970 input).mapErrors (.path "Born before 1970 user")

deriving instance ToString for Field

-- ~3 min
def report (t : TreeError) : String :=
  let rec indent (i : Nat) (t : TreeError) : String :=
    let space : String := List.replicate i "  " |> String.join
    match t with
    | .field field msg => s!"{space}❌ Problem with {field}: {msg}"
    | .path path t =>s!"{space}{path}\n{indent (i + 1) t}"
    | .both t1 t2 => s!"{indent i t1}\n{indent i t2}"
  indent 0 t

instance : ToString TreeError where
  toString := report

#print LegacyCheckedInput
instance : ToString LegacyCheckedInput where
  toString
  | .company name => s!"{name}"
  | .humanAfter1970 year name => s!"{year} {name}"
  | .humanBefore1970 year name => s!"{year} {name}"

instance : ToString (Validate TreeError LegacyCheckedInput) where
  toString
  | .ok valid => s!"{valid}"
  | .errors errs => s!"There were some errors:\n{errs}"

deriving instance Repr for TreeError
-- deriving instance Repr for Validate

#eval checkLegacyInput {name := "Joe", birthYear := "1972"}
def t1 := checkLegacyInput {name := "", birthYear := "1972"}
#eval t1
#eval checkLegacyInput {name := "Joe", birthYear := "1969"}
#eval checkLegacyInput {name := "", birthYear := "1969"}
#eval checkLegacyInput {name := "", birthYear := "FIRM"}
#eval checkLegacyInput {name := "ACME", birthYear := "FIRM"}
def t2 := checkLegacyInput {name := "ACME", birthYear := "999"}
#eval t2
#eval checkLegacyInput {name := "", birthYear := "1970"}

-- 53:57 min + 17:45 min + 59:37 min 🐌
end ImproveValidate

-- # Universes

#check Type
#check Prop

/- Having sets to be constructed by arbitrary properties
  allows weird membership relations and leads to Russel's
  paradox.

  Due to a similar paradox of dependent type theory,
  [Type] cannot itself be a member [Type]: [Type : Type]
  leads to logical inconsistencies.

  Therefore, another distinct type must was devised to
  accomodate [Type], and another, more general type to
  accomodate the type that accomodates [Type], etc.

  The container of [Type] is called [Type 1].
-/
#check Type

-- And the container of [Type 1] is [Type 2] and so on
#check Type 1
#check Type 2
#check Type 3

/-
  Note that your checking the type of types (cool, huh?).

  The proper terminology for these higher-kinded types is
  _universes_. The very first universe is [Type], which can
  also be read as [Type 0], but the [0] is omitted for brevity.

  Arrow types occupy the smallest universe that can
  accomodate both the argument type and the return type,
  so the maximum of the two universes plus one:
-/
#check Type 0
#check Nat → Nat
#check Nat → Type 1
#check Type → Type
#check Type 1 → Type 1
#check Type 1 → Type 2
#check Type 4 → Type 2
#check Prop → Prop
#check Prop → Type
#check Type → Prop

/- If the return type is _a_ [Prop], then the whole function
   type lives in [Prop], even if an argument type lives in
   a larger universe, such as [Type], [Type 1] etc. -/
#check (n : Nat) → n = n + 0
#check Nat
#check (α β : Type) → α = β -- Not [Type 1]!
#check Type 2 → 2 + 2 = 5 -- Not [Type 3]!

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α

#check MyList -- a function from [Type] to [Type].
/- An implication of the type of [MyList] is that it
  cannot be used to create a list of types.

  This is because it expects argument of type [Type], such
  as [Nat], [MyList Nat], [Unit] etc.
  To see why, the argument [Type] has [Type 1], which is larger than the expected argument type [Type] and leads
  to a type mismatch error:
-/
def myListOfTypes : MyList Type := -- Error
  .cons Nat (.cons String (.nil))

def myListofLists : MyList (MyList Nat) :=
  .cons .nil (.cons (.cons 1 .nil) .nil) -- [[],[1]]

#check Type 1 → Type
/-
  If we want list of types, we must lift the whole
  funtion type to one universe above.

  Both the argument and return type must be lifted.

  inductive MyTypeList (α : Type 1) : Type where
  | nil : MyTypeList α
  | cons : α → MyTypeList α → MyTypeList α

  The argument with type [α] is in a larger universe than [MyTypeList α] itself, and Lean rejects this definition.

  We solve this by increasing by one the level of the return
  type aswell.
-/
inductive MyTypeList (α : Type 1) : Type 1 where
  | nil : MyTypeList α
  | cons : α → MyTypeList α → MyTypeList α

#check MyTypeList.cons
def myListOfTypes' : MyTypeList Type :=
  .cons Nat (.cons String (.cons Unit .nil))

def myListOfLists : MyTypeList (MyTypeList Type) :=
  .cons .nil (.cons (.cons Nat .nil) .nil) -- [[], [Nat]]

/- But now we've rendered [MyTypeList] impossible to use
  in contexts that expect a [Type]. -/
#check MyTypeList Nat
#check MyTypeList.cons 1 .nil -- Hangs up with a metavariable
#check MyTypeList.cons 1 (MyTypeList.cons 2 .nil)

-- Defining a datatype in a _fixed_ universe can lead to code duplication.

-- # Universe Polymorphism
#check List -- Lean's [List] can accomodate [Type]s and higher classes thanks to the universe parameter [u]

/- It uses a feature called _universe polymorphism_ that works
  at a higher plain than ordinary polimorphism.

  Similarly to how ordinary polymorphism allows your definitions to contain type types variables (but the level is fixed),
  universe polymorphism allows variables to stand for universes
  in a definition.

  While we range over type variables with greek letters,
  we range over universe variables with latin letters [u], [v] and [w]. You can introduce a universe variable to stand for
  "any level". -/

inductive MyListU (α : Type u) : Type u where
  | nil : MyListU α
  | cons : α → MyListU α → MyListU α

/- [MyListU] can be used to contain actual natural numbers
  (level 0) and the type of natural numbers (level 1).
  In two separate definition, of course. The two types cannot be
  mixed in the same list. -/
example : MyListU Nat := .cons 1 .nil
example : MyListU Type := .cons Nat .nil
-- It can even contain itself (level 1)!
example : MyListU (Type → Type) :=
  .cons MyListU (
    .cons (fun t => MyListU (t → Nat)) (
      .cons id .nil
    ))

/- Notice that [MyListU] implicitly takes a universe level
  argument. It is annotated as follows in its type:

  MyListU.{u} (α : Type u) : Type u

  Lean infers this argument behind the scenes whenver you apply
  [MyListU], but you can also provide them manually.
-/

example : MyListU.{0} Nat := .cons 1 (.cons 0 .nil)

example : MyListU.{1} Type := .cons Nat (.cons Unit .nil)

example : MyListU.{1} (Type → Type) :=
  .cons MyListU.{0} (
    .cons (fun t => MyListU.{0} (t → Nat)) (
      .cons id .nil
    )) -- Turns out it wasn't actually referring to itself, but to a lower kinded version of itself. This dodges the pardoxes caused by cyclic and self-referential types

-- [MyListU.{u}] cannot contain itself, for any [u]:
example : MyListU.{u} (Type u → Type u) :=
  .nil -- ❌

example : MyListU.{u+1} (Type u → Type u) :=
  .cons MyListU.{u+1} .nil -- ❌

example : MyListU.{u+1} (Type u → Type u) := -- ✔️
  .cons MyListU.{u} .nil

#check List Type
#check List (List Type)

#check [Nat, String, Unit, Prop] -- [: List Type]

/- [Type] isn't the only inhabitant of [Type 1]!
  There are many arrow types to keep her company. -/
#check [Type, Type, Nat → Type, Type → Type → Type] -- [: List (Type 1)]

-- Do not confuse list of lists _of_ types with list of list types. Nested lists don't increase the universe level.
#check [List Type, List (List Type)]
#check [[String], [Nat, Unit]]
#check [List Nat, [Nat]] -- Error

-- ## Multiple universes

inductive MySum (α : Type u) (β : Type u) : Type u where
  | inl : α → MySum α β
  | inr : β → MySum α β

example : MySum Nat Unit := MySum.inr ()
example : MySum Nat Prop := MySum.inr (2 + 2 = 4)
example : MySum Type Type := MySum.inr Nat
example : MySum (Type → Type) Type := MySum.inl MyList

/- Loosening the universe constraint allows to sum together types
  from different universes -/
inductive MySum' (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → MySum' α β
  | inr : β → MySum' α β

example : MySum' Nat Type := .inl 1
example : MySum' Nat Type := .inr Nat

/- I want to stress that functions among the type variables do not
  need a larger universe. -/
inductive MyWeirdSum (α : Type u) (β : Type u) : Type u where
  | inl : (α → α) → MyWeirdSum α β
  | inr : β → MyWeirdSum α β

/- But as soon as you introduce a type parameter to a constructor,
  its level increases by one, and the whole inductive type must reflect this increase. -/
inductive MyWeirdSum' (α : Type u) (β : Type u) : Type (u+1) where
  | inl {γ : Type u} : γ → α → MyWeirdSum' α β
  | inr : β → MyWeirdSum' α β

example : MyWeirdSum' Nat Unit := .inl "what" 1
example : MyWeirdSum' Nat Unit := .inl (2 + 2 = 4) 1

-- ## Prop

/- [Prop] is at the bottom of the universe hierarchy: it lives
   inside [Type 0] together with [Nat], [String], [List Nat] and so on. It classifies logical propositions

   However an important difference makes it stand out among its
   datatype siblings:
   - Its values are still _types_: [p : Prop] classifies what
     counts as convincing evidence of the proposition [p].
     In contrast, the values of its sibling [Nat] are just
     atomic numbers.
   - All evidences of a proposition type are equipotent, meaning
     it doesn't matter which particular value is used, what
     matters it that it exists and can be constructed.
     Clearly this is not the case for datatypes like [Nat]:
     a program of type [Nat] should be concerned about what
     [Nat] it returns.
-/
#check Prop
example : List.{0} Prop := [
  2 + 2 = 4,
  "Geronimo" ++ "Stilton" = "Geronimo Stilton"
]

/- [Prop] and [Type] are united in a single hierarchy called[Sort].
  Like [Type] it can take a universe level argument, where [0] stands
  for [Prop] and [u + 1] stands for [Type u]. So:

  Sort 0        := Prop
  Sort (u + 1)  := Type u
-/
#check Sort 1
#check CoeSort

-- [CoeSort] allows to write [Sort 2] in place of [Type 1]

namespace CompleteDefinitions
#print Function.comp
#print Function.const

-- Function.const β a := fun _ : β => a
-- Function.const β a b := (fun _ : β => a) b
-- Function.const := fun β a _ => a
#eval Function.const Nat true 1
#eval Function.const Nat true 2

class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → β → f α → f β :=
    Function.comp map (Function.const _)

/-
  (I swapped the names of the type variables in book's definition of [mapConst] for consistency)

  Explenation for [mapConst]:

  We're composing two functions: the output type of the second
  argument must equal the input type of the first argument.

  [Function.const] has type [(β : Sort v) → (b : β) → α → β],
  here it is applied to [_] to let Lean infer the input type
  automatically, so [Function.const _] has type [β → α → β],
  which is the same as [β → (α → β)]. The input type is [β] and
  the output type is [α → β].

  [map] has type [(α → β) → f α → f β]. The input type is [α → β] and its output type is [f α → f β].

  The output type of [Function.const _] perfectly matches the input type of [map], hence the composition works. It defines a new function from the input type of [Function.const _] to the output type of [map], i.e. a function of type [β → f α → f β].

  Its behaviour is obvious: it applies the constant function to the contents of a structure to yield a new structure whose contents are is set to the constant. Equivalent to:

  fun (x : α) (y : f β) => map (fun _ => x) y
-/

#eval [1, 2, 3].map (Function.const _ true)
#eval (Function.const _ "same") <$> [1, 2, 3]

/- Now onto the analysis of the universes of [Functor]'s signature. The type of the class [Type (max (u+1) v)] imparts that the structures that implement the [Functor] type class reside in a universe that's necessarily larger than the universe [u] of the input type. To see why:
-/

/- Recall that [Type u], [Type u → Type u] or any combination of
  arrows and [Type u] all reside in [Type (u+1)], for any [u]. -/
#check Type
#check Type → Type

/- Here the universe level returned can't be no less than (u+1)
  because a constructor has a type parameter at level [u].
-/
inductive MyBogusSum (α : Type u) (β : Type u) : Type (u+1) where
  | inl : {γ : Type u} → γ → MyBogusSum α β
  | inr : β → MyBogusSum α β

/- To see why the output type of [Functor] must be at least [v],
  consider another bogus type: -/
inductive MyBogusSumUV (α : Type u) (β : Type v) : Type (max (u+1) v) where
  | inl : {γ : Type u} → γ → MyBogusSumUV α β
  | inr : β → MyBogusSumUV α β

/- The second constructor builds values that carry a value of the
  universe [v], and this must be taken into account by the [Sum] type be selecting the greater between [u+1] and [v].

  Note that any value in the universe [v] is also in [v+1], [v+2] etc., so is also acceptable (however not recommended: your universes should be as small as possible!).
-/
inductive MyBogusSumUV1 (α : Type u) (β : Type v) : Type (max (u+2) (v+1)) where
  | inl : {γ : Type u} → γ → MyBogusSumUV1 α β
  | inr : β → MyBogusSumUV1 α β

/- Other arguments of [Functor.map] have their type built by
  applying the function [f], which lifts them to the universe [v].
  The class's return type must take this into account requiring that it inhabits at least level [v] or above.

  The same argument applies for the types inhabited by the [Applicative] and [Monad] classes.
-/

/- [SeqRight] and [SeqLeft] evaluate both of their arguments in sequence.
  [SeqRight] ([SeqLeft]) returns the result of its second (first) argument, the first (second) are evaluated merely for their effects.

  If used with a [Monad], they are equivalent to, respectively:

  do let _ ← E1; E2                   (seqRight)
  do let x ← E1; let _ ← E2; pure x   (seqLeft) - got it right!
-/
#print SeqRight.seqRight
#print SeqLeft.seqLeft

/- The definition of [Applicative] extends [Functor], [Pure], [Seq], [SeqRight] and [SeqLeft],
  providing default methods for [map], [seqLeft] and [seqRight]
  while leaving [pure] and [seq] up to the implementor.

  The default implementations act both as automatically-created code and specifications for correctness. An implementor ought to override them only if she can provide a more efficient,
  behaviorally equivalent definition.
-/

#check Function.const String id -- A function that given any string returns the identity
#eval Function.const String id "Coq" 42 -- A function that given any string returns the identity

#check (Function.const String) <$> [1, 2, 3] -- Three functions that return 1, 2, and 3 on any string input, respectively: the list is used as constants
#check (Function.const Nat id) <$> [1, 2, 3] -- A list of three identities: the list is used as inputs

/-
  [Applicative]'s default implementations of [seqLeft] and [seqRight] are very ingeneous:

  Analyzing [seqLeft]:

  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
           := fun a b => ((fun x _ => x) <$> a) <*> b -- should've added sugar earlier to help myself

  It first [maps] [Function.const _] to [a] to get a "collection" of constant functions that return [a], whatever their input is.
  [_] is left to be inferred by Lean and will match the element type of [b].
  Then [Seq.seq] feeds [b] to this collection of constant functions. The values of [b] are discarded by each function,
  and the values of [a] are returned accordingly.
  [b] is evaluated nonetheless in order to be processed.


  This behavior agrees with the specification that it evaluates [a] then [b] only for its side effects and returns the result of [a].

  Analyzing [seqRight]:

  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
           := ((fun _ => id) <$> a) <*> b
           := ((fun _ => fun x => x) <$> a) <*> b
           := ((fun _ x => x) <$> a) <*> b

  The subtle difference in arguments gives rise to  the opposite effect.
  Here [id] is gets to be the return value of the constant functions and
  the values of [a] are going to be evaluated and thrown out, with the upside
  that its effects (if any) will occur.
  Then the identities become the first argument to [Seq.seq], who in turn
  feeds them [b]. [b] will be evaluated and its result returned untouched.
-/

/- Lastly, the [Monad] type class just add the [bind] operation to
  the mix. [bind] is defined externally in the type class [Bind].
  As a result, it extends both [Applicative] and [Bind], yielding natural implementations for [map], [seq], [seqLeft] and [seqRight] in terms of [bind].
-/
class Monad (m : Type u → Type v) extends Bind m, Applicative m where
  map f m := m >>= fun x => pure (f x) -- or [m >>= pure ∘ f]
  seq a b      := a >>= fun f => b () >>= fun x => pure (f x) -- or [a >>= fun f => f <$> b ()]
  seqLeft  a b := a >>= fun x => b () >>= fun _ => pure x
  seqRight a b := a >>= fun _ => b ()
-- ~5 min

end CompleteDefinitions
