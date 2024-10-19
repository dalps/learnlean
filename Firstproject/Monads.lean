-- # Chaining options
namespace Maybe

def first (xs : List α) : Option α :=
  xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some x0 => match xs[2]? with
               | none => none
               | some x2 => some (x0,x2)

#eval firstThird [2,3,5,7]

def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some x0 => match xs[2]? with
               | none => none
               | some x2 => match xs[4]? with
                            | none => none
                            | some x4 => some (x0,x2,x4)

-- This is getting out of hand... let's try to improve on this:

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

/- [andThen] introduces a new pattern: fed with an optional value,
   if it contains something then [andThen] applies the supplied function to its content, otherwise it returns [none].
   -/
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  andThen xs[0]? (fun x0 =>
    andThen xs[2]? (fun x2 =>
      andThen xs[4]? (fun x4 =>
        andThen xs[6]? (fun x6 => some (x0, x2, x4, x6)))))

/- Still horrible to type out (~10 min without peeking).
   Luckily there's no need for parentheses nor indentation!
   Now we have a pipeline for options. The version without the unnecessary syntax is more evocative of the flow of values: -/

def firstThirdFifthSeventh' (xs : List α) : Option (α × α × α × α) :=
  andThen xs[0]? fun x0 =>
  andThen xs[2]? fun x2 =>
  andThen xs[4]? fun x4 =>
  andThen xs[6]? fun x6 => some (x0, x2, x4, x6)

-- Let's define an infix operator

infixl:55 " ~~> " => andThen -- the higher the number, the higher the precedence (covariant).
-- Higher-precedence operators are applied before lower-precedence ones.n

-- The infix operator evinces the pipeline feeling of none-handling
def firstThirdFifthSeventh'' (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)

end Maybe

-- # Handling exceptions
namespace Exception

-- Lean's equivalent of OCaml's [('a,'e) Result]
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
deriving Repr, Hashable, Repr

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"get failed: index {i} is not within 0..{xs.length-1}"
  | some x => Except.ok x

#eval get [1,2,3] 3

def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]

#eval get ediblePlants 3
#eval get ediblePlants 4

/- Let's define chains of lookups again,
   handling [Except] values this time around -/

def first (xs : List α) : Except String α :=
  get xs 0

def firstThirdBad (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok x0 => match get xs 0 with
                    | Except.error msg => Except.error msg
                    | Except.ok x2 => Except.ok (x0, x2)

def andThen (attempt : Except ε α) (next : α -> Except ε β) : Except ε β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x

infixl:55 " ~~> " => andThen

def firstThird (xs : List α) : Except String (α × α) :=
  get xs 0 ~~> fun x0 =>
  get xs 2 ~~> fun x2 =>
  Except.ok (x0, x2)

-- We can factor out the need to type constructors, for both success and failure
def ok (x : α) : Except ε α := Except.ok x

def fail (err : ε) : Except ε α := Except.error err

def get' (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"get failed: index {i} is not within 0..{xs.length-1}"
  | some x => ok x

def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)

#eval firstThirdFifthSeventh
ediblePlants

end Exception

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α -> α -> BinTree α -> BinTree α
deriving Repr

open BinTree
def tree : BinTree Int :=
  branch
    (branch leaf 2 leaf)
    1
    (branch
      (branch leaf 3
        (branch leaf 5 leaf))
      4
      leaf)

def tree2 : BinTree Int :=
  branch
    (branch
      (branch
        (branch
          (branch leaf 0 leaf)
          1
          leaf)
        2
        leaf)
      3
      (branch leaf (-3) leaf))
    4
    (branch leaf 5 leaf)

-- # Logging
namespace Logging

def isEven (i : Int) : Bool :=
  i % 2 == 0

  def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | x :: xs =>
    let (ys, sum) := sumAndFindEvens xs
    (if isEven x then x :: ys else ys, sum + x)

#eval sumAndFindEvens [0,2,4,6,8,10]
#eval sumAndFindEvens [0,1,2,4,7,6,1,21]

def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l v r =>
    let (nodesL, sumL) := inorderSum l
    let (hereVisited, hereSum) := ([v], v)
    let (nodesR, sumR) := inorderSum r
    (nodesL ++ hereVisited ++ nodesR, sumL + hereSum + sumR)

#eval inorderSum tree

-- Making the pattern more evident
def sumAndFindEvens' : List Int → List Int × Int
  | [] => ([], 0)
  | x :: xs =>
    let (moreEvens, sum) := sumAndFindEvens xs
    let (evenHere, ()) := (if isEven x then [x] else [], ())
    (evenHere ++ moreEvens, sum + x)
    /- Append the nodes currently available to the nodes accumulated so far,
       calculate the function's result using the information currently and
       the other information carried over -/

-- Pair of accumulated result and value
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
deriving Repr

-- ~10 min
def andThenUgly (result : WithLog Λ α) (next : α → WithLog Λ β) : WithLog Λ β :=
  let result' := next result.val
  {
    log := result.log ++ result'.log
    val := result'.val
  }

def andThen (result : WithLog Λ α) (next : α → WithLog Λ β) : WithLog Λ β :=
  let {log := thisOut, val := thisVal} := result
  let {log := nextOut, val := nextVal} := next thisVal
  {log := thisOut ++ nextOut, val := nextVal}

def ok (x : β) : WithLog α β := {log := [], val := x}

def save (data : α) : WithLog α Unit := {log := [data], val := ()}

-- ~18 min
def sumAndFindEvens'' : List Int → WithLog Int Int
  | [] => ok 0
  | x :: xs =>
    -- Inverting the order of the two lines inverts the order of the log (try it!). The sum, of course, stays the same
    andThen (sumAndFindEvens'' xs)                fun sum =>
    andThen (if isEven x then save x else ok ())  fun () =>
    ok (x + sum)

#eval sumAndFindEvens [0,2,4,6,8,10]
#eval sumAndFindEvens [0,1,2,4,7,6,1,21]

#eval sumAndFindEvens'' [0,2,4,6,8,10]
#eval sumAndFindEvens'' [0,1,2,4,7,6,1,21]

-- ~5 min
def inorderSum' : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l v r =>
    andThen (inorderSum' l) fun leftSum =>
    andThen (save v)        fun () =>
    andThen (inorderSum' r) fun rightSum =>
    ok (leftSum + v + rightSum)

#eval inorderSum tree
#eval inorderSum' tree

-- [inorderSum] logs the left branch first then the root and finally the right branch
#eval inorderSum' tree2

infixl:55 " ~~> " => andThen

def sumAndFindEvens''' : List Int → WithLog Int Int
  | [] => ok 0
  | x :: xs =>
    (if isEven x then save x else ok ())
    ~~> fun () => (sumAndFindEvens''' xs)
    ~~> fun sum => ok (sum + x)

def inorderSum'' : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l v r =>
    inorderSum'' l ~~> fun leftSum =>
    save v         ~~> fun () =>
    inorderSum'' r ~~> fun rightSum =>
    ok (leftSum + v + rightSum)

#eval sumAndFindEvens''' [0,2,4,6,8,10]
#eval sumAndFindEvens''' [0,1,2,4,7,6,1,21]
#eval inorderSum'' tree2

end Logging

def aTree :=
  branch
    (branch
      (branch leaf "a" (branch leaf "b" leaf))
      "c"
      leaf)
    "d"
    (branch leaf "e" leaf)

-- Get the rightmost value in the tree
def descendRight (t : BinTree α) : Option α :=
  let rec helper (acc : Option α) (t' : BinTree α) :=
    match t' with
    | leaf => acc
    | branch _ v r => helper (some v) r
  match t with
  | leaf => none
  | branch _ v r => helper v r

#eval descendRight tree
#eval descendRight tree2
#eval descendRight aTree

-- # Numbering a tree in an inorder fashion
/- First attempt:
def tryNumbering : BinTree Int -> BinTree (Nat × Int)
  | leaf => leaf
  | branch l v r =>
    Maybe.andThen (tryNumbering l |> descendRight) fun (leftMax, _) =>
    Abort -- stuck... (bad approach) -/

-- ~20 min
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (num : Nat) (t : BinTree α) : (Nat × BinTree (Nat × α)) :=
    match t with
    | leaf => (num, leaf)
    | branch l v r =>
      let (numLeft, numberedLeft) := helper num l
      let numThis := numLeft
      let (numRight, numberedRight) := helper (numThis + 1) r
      (numRight, branch numberedLeft (numThis, v) numberedRight)
  (helper 0 t).snd

#eval number aTree
#eval number tree
#eval number tree2

-- # Stateful computations
namespace Stateful

/- The thing we want to propagate now is a [State] for a single mutable
   variable, whose values are functions.
   These functions take an input state and return an output state together
   with a value. Reading preserves the state, whereas writing replaces it
   with a new one. -/
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)

def set (x : σ) : State σ Unit :=
  fun _ => (x, ())

-- Sequencing of stateful operations (~10 min)
def andThen (first : State σ α) (next : α -> State σ β) : State σ β :=
  fun s0 =>
    let (s1, a) : σ × α := first s0
    let S : State σ β := next a
    S s1

infixl:55 " ~~> " => andThen

-- ~52 min, peeked a lot
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | leaf => ok leaf -- Base state
    | branch l v r =>
      helper l        ~~> fun numberedLeft =>
      get             ~~> fun numL =>
      set (numL + 1)  ~~> fun () =>
      helper r        ~~> fun numberedRight =>
      ok (branch numberedLeft (numL, v)  numberedRight)
  (helper t 0).snd
  /-  I'm embarassed of this attempt
      let f :=
        set 0 ~~> fun () =>
        ok t  ~~> helper
              ~~> fun numbered =>
        ok numbered -- How do I escape from a [State]!?
      f 0 -/

#eval number tree
#eval number aTree

end Stateful

-- # The monad type class
namespace Monad

instance : Monad Option where
  pure := some
  bind := Maybe.andThen

instance : Monad (Exception.Except ε) where
  pure := Exception.ok
  bind := Exception.andThen

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

-- This very general lookup function can be used with any instance of [Monad]

def slowMammals : List String :=
  ["Three-toead sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventh List.get? slowMammals
#eval firstThirdFifthSeventh List.get? fastBirds

#eval firstThirdFifthSeventh Exception.get slowMammals
#eval firstThirdFifthSeventh Exception.get fastBirds

-- 14:16 min
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun y =>
    mapM f xs >>= fun ys =>
    pure (y :: ys)

#eval mapM some slowMammals

/- Just like the instance of [Excpet] mentioned a type [ε] for the error
   messages that becomes a parameter to the instance, the state type
   [σ] now becomes an instance parameter of [State].

   This means that, when sequencing [State] values, the type of the state
   cannot change, which is a reasonable rule. -/

instance : Monad (Stateful.State σ) where
  pure := Stateful.ok
  bind := Stateful.andThen

open Stateful
def increment (howMuch : Int) : State Int Int :=
  get >>= fun x =>
  set (x + howMuch) >>= fun () =>
  pure x -- if you return [get] you shift the partial sum by the first element

instance [ToString α] : ToString (State Int α) where
  toString f := s!"{f 0}, {f 1}, {f 2}..."

#check mapM increment
#eval mapM increment [1, 2, 3, 4, 5]
#eval mapM increment [1, 2, 3, 4, 5] 0
#eval mapM increment [1, 2, 3, 4, 5] 1

instance : Monad (Logging.WithLog Λ) where
  pure := Logging.ok
  bind := Logging.andThen

open Logging
def logIfEven (x : Int) : WithLog Int Int :=
  (if isEven x then
    save x
    else pure ()) >>= fun () =>
  pure x

#eval mapM logIfEven [1, 2, 3, 4, 5]

def logIfStartsWith (pre : String) (s : String) : WithLog String String :=
  (if String.startsWith s pre then
    save s
    else pure ()) >>= fun () =>
  pure s

#eval mapM (logIfStartsWith "S") fastBirds
#eval mapM (logIfStartsWith · "A") fastBirds

class LogIf (p : α → Bool) where
  logIf (x : α) : WithLog α α :=
    (if p x then
      save x
      else pure ()) >>= fun () =>
    pure x

-- Monads encode programs with effects

-- Or no effects at all, i.e. pure computations:
def Id (t : Type) : Type := t -- Identity on types

instance : Monad Id where
  pure x := x -- [pure : α → Id α], i.e. [α → α]
  bind x next := next x -- [bind : Id α → (α → Id β) → Id β], i.e. [α → (α → β) → β]
  -- [next] doensn't change the type

-- With the identity monad, [mapM] is equivalent to [map]
#eval mapM (· + 1) [1, 2, 3, 4, 5] -- not quite right, need to fiddle with the implicit instance
#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]
#eval mapM (fun x => x) [1, 2, 3, 4, 5] -- Lean can't figure out what kind of monad we want

-- # Lawful monads

/- Every instance of [Monad] should obey three rules:

    1. [pure] is a left identity of [bind]: [bind (pure v) f = v]
    2. [pure] is a right identify of [bind]: [bind v pure = v]
    3. [bind] is associative: [bind (bind v f) g = bind v (fun w => bind (f w) g)],
       or [(v >>= f) >>= g = v >>= (fun w => f w >>= g)]

    These rules ensure that:
    * [pure] is the program with no side-effects
    * sequencing effects with [pure] and [bind] doesn't change the result
    * the sequencing bookkeping itself doesn't matter, so long as the order
      in which things are happening (first [f], then [g]) is preserved.
-/

#eval mapM (m := Id) (fun x : Nat => x) ([1, 2, 3, 4, 5])

end Monad

#check List.mapM

-- 12:30 min
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure (BinTree.leaf)
  | BinTree.branch left x right =>
    left.mapM f  >>= fun left'  =>
    f x          >>= fun x'     =>
    right.mapM f >>= fun right' =>
    pure (BinTree.branch left' x' right')

#eval aTree.mapM (Monad.logIfStartsWith "a")
#eval tree.mapM Monad.logIfEven
#eval tree2.mapM some

/- The [Monad] instance for [Option]: -/ -- Ending a commend with : is buggy

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

/- satisfies the monad contract.
    Proof:

    1. [some] is a left identity for [bind]

       bind (pure x) f = f x
       bind (some x) f = f x  -- Definition of [pure]
       f x = f x              -- Definition of [bind], case [some]

    2. [some] is a right identity for [bind]

       bind v pure = v
       bind v some = v

       - If [v = none], then [bind v some = none]

         bind none some = none
         none

       - Otherwise [v = some x] for some [x], and

         bind (some x) some = some x
         some x = some x

       In both cases, the two sides are equal.

    3. [bind] is associative:

       bind (bind x f) g = bind x (fun y => bind (f y) g)

       By analysis on the shape of [x]:

       - [x = none]

          bind (bind none f) g = bind none (fun y => bind (f y) g)
          bind none g = none
          none = none

       - [x = some y]

          bind (bind (some y) f) g = bind (some y) (fun z => bind (f z) g)
          bind (f y) g = (fun z => bind (f z) g) y
          bind (f y) g = bind (f y) g

       We have an equality in both cases.
-/

instance : LawfulMonad Option where
  pure_bind := by sorry
  bind_assoc := by sorry
  bind_map := by sorry
  bind_pure_comp := by sorry

/-
  The instance where [bind] is [none] on any input is unlawful.

  instance : Monad Option where
    pure x := some x
    bind opt next := none

  It violates the first rule for the function [some]:

    bind (some x) some = some x
    none = some x

  and also the second rule for [x = some x']:

    bind x pure = x
    bind x some = x
    none = some x'

  while it is preserves associativity.
-/
#check LawfulMonad

-- # Arithmetic expressions
namespace ArithExpr

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Arith where
  | plus
  | minus
  | times
  | div

-- Expressions are binary trees
open Expr Arith

def twoPlusThree : Expr Arith := prim plus (const 2) (const 3)

def fortyPlusTwo : Expr Arith :=
  prim plus (prim times (const 10) (const 4)) (const 2)

def fourteenDivided : Expr Arith :=
  prim div (const 14)
    (prim minus (const 45) (prim times (const 5) (const 9)))

-- # Evaluation with Option
namespace WithOption

-- ~5 min
def evaluateOption' : Expr Arith → Option Int
  | const i => pure i
  | prim op left right =>
    evaluateOption' left >>= fun vl =>
    evaluateOption' right >>= fun vr =>
    match op with
    | plus =>  pure (vl + vr)
    | minus => pure (vl - vr)
    | times => pure (vl * vr)
    | div => if vr == 0 then none else pure (vl / vr)

#eval evaluateOption' fortyPlusTwo
#eval evaluateOption' fourteenDivided

def applyPrim : Arith → Int → Int → Option Int
  | plus, x1, x2 => pure (x1 + x2)
  | minus, x1, x2 => pure (x1 - x2)
  | times, x1, x2 => pure (x1 * x2)
  | div, x1, x2 => if x2 == 0 then none else pure (x1 / x2)

def evaluateOption : Expr Arith → Option Int
  | const i => pure i
  | prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    applyPrim p v1 v2
end WithOption


def divFail (x : Int) : Except String Int :=
  Except.error s!"Tried to divide {x} by zero"

-- # Evaluation with Except
-- Let's return a meaningful error message
namespace WithExcept

-- Note: using Lean's [Except] API
def applyPrim : Arith → Int → Int → Except String Int
  | plus, x1, x2 => pure (x1 + x2)
  | minus, x1, x2 => pure (x1 - x2)
  | times, x1, x2 => pure (x1 * x2)
  | div, x1, x2 =>
    if x2 == 0 then
      divFail x1
    else pure (x1 / x2)

def evaluateExcept : Expr Arith → Except String Int
  | const i => pure i
  | prim p e1 e2 =>
    evaluateExcept e1 >>= fun v1 =>
    evaluateExcept e2 >>= fun v2 =>
    applyPrim p v1 v2

/- The downside of this evaluator is having to rewrite two
   definitions every time I want a different effect.

   Can the effect be factored out then? Yes, by making it polymorphic over its monad! -/
end WithExcept

-- # Abstacting over any monad
def applyPrimOption := WithOption.applyPrim
def applyPrimExcept := WithExcept.applyPrim

/- By moving the operator logic to [applyPrim], [evaluate] doesn't
   have to worry of handling errors, and the two methods of
   [Monad] suffice to define it. Moreover, by abstracting over
   [applyPrim] itself, it can achieve any side-effect. -/
def evaluateM' [Monad m] (applyPrim : Arith → Int → Int → m Int) : Expr Arith → m Int
  | const i => pure i
  | prim p e1 e2 =>
    evaluateM' applyPrim e1 >>= fun v1 =>
    evaluateM' applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2

def evaluateOption := evaluateM' applyPrimOption
def evaluateExcept := evaluateM' applyPrimExcept

#eval evaluateOption fourteenDivided
#eval evaluateExcept fourteenDivided

-- # Abstracting over division
def applyDivOption (x : Int) (y : Int) : Option Int :=
  if y == 0 then
    none
  else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
  if y == 0 then
    divFail x
  else pure (x / y)

def applyPrim [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | plus,  x, y => pure (x + y)
  | minus, x, y => pure (x - y)
  | times, x, y => pure (x * y)
  | div,   x, y => applyDiv x y

def evaluateM [Monad m] (applyDiv : Int → Int → m Int) : Expr Arith → m Int
  | const i => pure i
  | prim p e1 e2 =>
    evaluateM applyDiv e1 >>= fun v1 =>
    evaluateM applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2

namespace Special
/- The two code paths differ only in their treatment of error,
   in particular when dividing two numbers. If error can occur
   in other operators, it might be more convenient to leave [applyPrim] as specialized as it was.

   To cover more interesing effects, additional refactoring is
   beneficial. -/

-- # Abstracting over any effectful operation
inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

/- [other] is an effort to categorize the effects operators other
   than the "pure" ones ([plus], [minus], [times]) bring about. -/

inductive CanFail where
  | div

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y => if y == 0 then divFail x else pure (x / y)

/- [evaluateM] depends on [applyPrim] and therefore on any
   parameter of [applyPrim].

   Note: [special] is an implicit type parameter of [applyPrim]. -/
def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Prim special) → m Int
  | const i => pure i
  | prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2

-- # No effects at all

/- Using the [Empty] type as the parameter [special] of [Prim]
   we forbid the evaluation of operators beyond [plus], [minus]
   and [times], because it is impossible to place a value of
  type [Empty] within the [other] constructor.

   The argument to [applySpecial] when [special] is [Empty]
   stands for dead code: code that neither can be called nor
   it returns a result. Passing [applyEmpty] to [evaluateM]
   signals that [evaluateM] and instantiating the instance
   implicit monad with [Id] allows us to evaluate expressions
   that are free of effects.
-/
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op -- Like [exfalso]: when one of your premises is false, you can imply false

open Expr Prim
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))
#eval evaluateM (m := Id) applyEmpty (prim (other CanFail.div) (const 5) (const (-14)))
#eval evaluateM divExcept (prim (other CanFail.div) (const 5) (const (-14)))
#eval evaluateM divOption (prim (other CanFail.div) (const 42) (const (-14)))
end Special

-- # Recovering from failure
namespace NonDeterministic

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

instance : Coe α (Many α) where
  coe := Many.one

-- ~5 min
def Many.union : Many α → Many α → Many α
  | none, m => m
  | more one others, m => more one (fun () => (others ()).union m)

#check (Many.union "calico" "siamese" : Many String)

def multi1 : Many Int := Many.union (1 : Int) (2 : Int)

def Many.fromList : List α → Many α
  | [] => none
  | x :: xs => Many.more x (fun () => fromList xs)

-- ~5 min
def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, none => []
  | n + 1, more x xs => x :: ((xs ()).take n)

def Many.takeAll : Many α → List α
  | none => []
  | more x xs =>  x :: (xs ()).takeAll

#eval multi1.take 24
#eval multi1.takeAll

def Many.pure : α → Many α := Many.one

def Many.bind : Many α → (α → Many β) → Many β
  | none, _ => none -- Nothing to combine, return nothing
  | more x xs, next =>
    Many.union (next x) (bind (xs ()) next)

/- [Many.one] and [Many.bind] obey the monad contract:

  1. [Many.one] is a left identity for [Many.bind]
  bind (one v) f = f v
  bind (more v (fun () => none)) f = f v
  union (f v) (bind none f) = f v
  union (f v) none = f v
  f v = f v -- The empty multiset is a right identity of [union]

  2. [Many.one] is a right identity for [Many.bind]
  bind v one = v -- By induction on [v]

  * bind none one = none
    none = none

  * bind (more x xs) one = more x xs
    union (one x) (bind (xs ()) one) = more x xs
    {v1} ⋃ {v2} ⋃ {v3} ⋃ ... ⋃ {vn} = more x xs

  3. [Many.bind] is associative
  bind (bind v f) g = bind v (fun y => bind (f y) g)

  * bind (bind none f) g = bind none (fun y => bind (f y) g)
    none = none

  * bind (bind v f) g
    bind (bind {v1, v2, v3, ..., vn} f) g =
    bind (f v1 ⋃ f v2 ⋃ f v3 ... ⋃ f vn) g =
    bind {v1₁, ..., v1ₙ₁,
          v2₁, ..., v2ₙ₂,
          v3₁, ..., v3ₙ₃,
          ...
          v3₁, ..., v3ₙₘ,} g =
    (g v1₁ ⋃ ... ⋃ g v1ₙ₁ ⋃
     g v2₁ ⋃ ... ⋃ g v2ₙ₂ ⋃
     g v3₁ ⋃ ... ⋃ g v3ₙ₃ ⋃
     ...
     g v3₁ ⋃ ... ⋃ g v3ₙₘ) =
    (g v1₁ ⋃ ... ⋃ g v1ₙ₁) ⋃
    (g v2₁ ⋃ ... ⋃ g v2ₙ₂) ⋃
    (g v3₁ ⋃ ... ⋃ g v3ₙ₃) ⋃
     ...
    (g v3₁ ⋃ ... ⋃ g v3ₙₘ) = -- Since [Many.union] is associative
    bind (f v1) g ⋃
    bind (f v2) g ⋃
    bind (f v3) g ⋃
    ...           ⋃
    bind (f vn) g = -- fg := fun x => bind (f x) g
    fg v1 ⋃ fg v2 ⋃ fg v3 ... ⋃ fg vn =
    bind {v1, v2, v3, ..., vn} fg =
    bind v (fun x => bind (f x) g) =
-/

#check LawfulMonad

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

/- This monad is *really* powerful. With it, we can create an example
   search that finds all the combinations of numbers in a list
   that add to 15. -/

-- 1:15 h - peeked a lot :( but at least I got the intuition right
def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun sum =>
         pure (x :: sum))

/- THIS IS NOT EQUIVALENT AT ALL!
    (addsTo goal xs).union $
    if x > goal then
      addsTo (goal - x) xs >>= fun sum =>
      pure (x :: sum)
    else
      Many.none -- [x] won't be included in any sum
-/

-- [addsTo (goal - x) xs] is all the sublists whose sum is [goal - x]
#check addsTo
#eval (addsTo 15 [1,2,3,4,5]).takeAll
#eval (addsTo 15 [1,2,3,4,5,10]).takeAll
#eval (addsTo 15 [1,2,3,4,5,10,0]).takeAll
#eval (addsTo 15 [0,1,2,3,4,5,10]).takeAll
#eval (addsTo 15 [0,0,1,2,3,4,5,10]).takeAll
#eval (addsTo 15 [0,0,0,1,2,3,4,5,10]).takeAll
#eval (addsTo 15 [0,0,0,0,0,0,0,0,1,2,3,4,5,10]).takeAll -- It's fast!
-- #eval Many.take 10 <| addsTo 15 <| (List.replicate 100 0).append [1,2,3,4,5] -- Stack overflow
#eval (addsTo 15 []).takeAll
#eval (addsTo 15 [1,2,3,4]).takeAll
#eval (addsTo 15 [3,9,15]).takeAll


end NonDeterministic

-- Without effects, calculators would be useless

end ArithExpr
