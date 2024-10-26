import Firstproject.NonEmptyList

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
  orElse
    | none, b => b ()
    | some a, _ => .some a
