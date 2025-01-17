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

instance : Monad (Except ε) where
  pure := Except.ok
  bind := andThen

/- 25:56 min
  [Except ε] obeys the monad contract

  1.
  bind (pure v) f = f v
  ===>
  bind (Except.ok v) f
  ===>
  match Except.ok v with
  | ...
  | Except.ok x => f x
  ===>
  f v

  2.
  bind v pure = v
  ===>
  bind v Except.ok = v
  ===>
  match v with
  | Except.error msg => Except.error msg
  | Except.ok x => Except.ok x

  Clearly, both cases return the input itself.

  3.
  bind (bind v f) g = bind v (fun x => bind (f x) g)

  bind (bind v f) g
  ===>
  match bind v f with
  | Except.error msg => Except.error msg
  | Except.ok z => g z
  ===>
  match
    match v with
    | Except.error msg => Except.error msg
    | Except.ok y => f y
  with
  | Except.error msg => Except.error msg
  | Except.ok z => g z

  ###

  bind v (fun x => bind (f x) g)
  ===>
  match v with
  | Except.error msg => Except.error msg
  | Except.ok y => (fun x => bind (f x) g) y
  ===>
  match v with
  | Except.error msg => Except.error msg
  | Except.ok y =>
    (fun x =>
      match f x with
      | Except.error msg => Except.error msg
      | Except.ok z => g z) y
  ===>
  match v with
  | Except.error msg => Except.error msg
  | Except.ok y =>
    match f y with
    | Except.error msg => Except.error msg
    | Except.ok z => g z

  When [v = Except.ok y], matching on [f y] in the scrutinee or when
  [v] is inspected have the same result.

  * Assume [v = Except.error msg] for some [msg]. Then it is easy to
    see that both expression evaluate to [Except.error msg].

  * Assume [v = Except.ok x] for some [x]. Then

    match
      match Except.ok x with
      | Except.error msg => Except.error msg
      | Except.ok y => f y
    with
    | Except.error msg => Except.error msg
    | Except.ok z => g z
    ===>
    match f y with
    | Except.error msg => Except.error msg
    | Except.ok z => g z

    is equal to

    match Except.ok x with
    | Except.error msg => Except.error msg
    | Except.ok y =>
      match f y with
      | Except.error msg => Except.error msg
      | Except.ok z => g z
    ===>
    match f y with
    | Except.error msg => Except.error msg
    | Except.ok z => g z.

    Qed.
-/
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
  fun s =>
    let (s', x) := first s
    next x s'

instance : Monad (State σ) where
  pure := ok
  bind := andThen

/- 42:10 min
  [State σ] obeys the monad contract:

  1.
  bind (pure v) f = f v

  bind (pure v) f
  ===>
  bind (fun s => (s,v)) f
  ===>
  fun s =>
    let (s',x) := (fun s => (s,v)) s
    f x s'
  ===>
  fun s =>
    let (s',x) := (s,v)
    f x s'
  ===>
  fun s => f v s
  ===> [∀ g, fun x => g x = g with g = f v]
  f v

  2.
  bind v pure = v

  bind v pure
  ===>
  bind v (fun x => fun s => (s, x))
  ===>
  fun s =>
    let (s',x) := v s
    (fun x => fun s => (s, x)) x s'
  ===>
  fun s =>
    let (s',x) := v s
    (s',x)
  ===>
  fun s => v s
  ===>
  v

  3.
  bind (bind v f) g = bind v (fun x => bind (f x) g)

  bind (bind v f) g
  ===>
  fun s =>
    let (s',x) := (bind v f) s
    g x s'
  ===>
  fun s =>
    let (s',x) := (fun r =>
                      let (s',x) := v r
                      f x s'
                  ) s
    g x s'
  ===>
  fun s =>
    let (s',x) := let (s',x) := v s
                  f x s'
    g x s'
  ===>
  fun s =>
    let (s',x) := f (v s).snd (v s).fst
    g x s'
  ===>
  fun s =>
    g (f (v s).snd (v s).fst).snd
      (f (v s).snd (v s).fst).fst
  ===>
  Assume [v = fun s => (r,x)] for any [r], [x]:

  fun s =>
    g (f ((fun s => (r,x)) s).snd ((fun s => (r,x)) s).fst).snd
      (f ((fun s => (r,x)) s).snd ((fun s => (r,x)) s).fst).fst
  ===>
  fun s =>
    g (f (r,x).snd (r,x).fst).snd
      (f (r,x).snd (r,x).fst).fst
  ===>
  fun s =>
    g (f x r).snd (f x r).fst

  ###

  bind v (fun x => bind (f x) g)
  ===>
  fun s =>
    let (s',x) := v s
    (fun x => bind (f x) g) x s'
  ===>
  fun s =>
    let (s',x) := v s
    (bind (f x) g) s'
  ===>
  fun s =>
    (bind (f (v s).snd) g) (v s).fst
  ===>
  fun s =>
    (fun r =>
      let (s',x) := (f (v s).snd) r
      g x s'
    ) (v s).fst
  ===>
  fun s =>
    let (s',x) := (f (v s).snd) (v s).fst
    g x s'
  ===>
  fun s =>
    g ((f (v s).snd) (v s).fst).snd
      ((f (v s).snd) (v s).fst).fst
  ===>
  Assume [v = fun s => (r,x)] for *the same* [r], [x]:

  fun s =>
    g ((f (( fun s => (r,x) ) s).snd) (( fun s => (r,x) ) s).fst).snd
      ((f (( fun s => (r,x) ) s).snd) (( fun s => (r,x) ) s).fst).fst
  ===>
  fun s =>
    g ((f (r,x).snd) (r,x).fst).snd
      ((f (r,x).snd) (r,x).fst).fst
  ===>
  fun s =>
    g ((f x) r).snd ((f x) r).fst
  ===> Application is left-associative
  fun s =>
    g (f x r).snd (f x r).fst

  Qed.
-/

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
#eval evaluateM (m := Id) applyEmpty (prim (other CanFail.div) (const 5) (const (-14))) -- [div] has effects
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

inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)

/- [evaluateM] and [applyPrim] are parameterized over a monad,
   [Many] is a monad instance. Non deterministic evaluation is
   possible with minimal code!
-/
open Special.Prim Expr NeedsSearch

-- 1 + choose(2,5)
#eval Many.takeAll <| Special.evaluateM applySearch
  (prim Special.Prim.plus
    (const 1)
    (prim (other choose) (const 2) (const 5)))

-- 1 + 2/0
#eval Many.takeAll <| Special.evaluateM applySearch
  (prim Special.Prim.plus
    (const 1)
    (prim (other div) (const 2) (const 0)))

-- 90 / (choose(-5,5) + 5)
#eval Many.takeAll <| Special.evaluateM applySearch
  (prim (other div)
    (const 90)
    (prim plus
      (prim (other choose) (const (-5)) (const 5))
      (const 5)))
end NonDeterministic

-- # Custom environments
namespace Env

-- A new monad, representing environments of functions and operators.
def Reader (ρ : Type) (α : Type) : Type := ρ → α -- [ρ] stands for environments, [α] is pretty much anything, such as an environment

def read : Reader ρ ρ := fun env => env

/- [ρ] could be seen as a collection of function names, while [α] as their
   implementations. The mapping from function names to their implementations
   is called an _environment_.

   The simplest environment is the one that when queried a constant, it
   returns the constant function. -/
def Reader.pure (x : α) : Reader ρ α := fun _ => x

/- Don't do this:
def Reader.bind : Reader ρ α → (α → Reader ρ β) → Reader ρ β :=
  You won't get Lean's Infoview help, because you didn't label
  your things. Also, remember to expand definitions, as in this case.

  When you're done, undo the expansion and clean the details.

def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env
-/
def Reader.bind (result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β :=
  -- Queries the [result] environment, does something with the result to form a new environment
  fun env => next (result env) env

/- [Reader.pure] and [Reader.bind] obey the monad contract.

    1.
    bind (pure v) f
    ==>
    fun env => f ((fun _ => v) env) env
    ==>
    fun env => f v env
    ==> -- Forall [g], [g = fun x => g x]. Here, take [g] as [f v], which can be applied to [env].
    f v

    2.
    bind r pure = r
    ==>
    fun env => pure (r env) env
    ==>
    fun env => (fun _ => (r env)) env
    ==>
    fun env => r env
    ==>
    r

    3.
    bind r (fun y => bind (f y) g)
    ==>
    fun env => (fun y => bind (f y) g) (r env) env
    ==>
    fun env => (bind (f (r env)) g) env
    ==>
    fun env => (fun env' => g (f (r env) env') env') env
    ==>
    fun env => g (f (r env) env) env
    =
    bind (bind r f) g
    ==>
    fun env => g ((bind r f) env) env
    ==>
    fun env => g ((fun env' => f (r env') env') env) env
    ==>
    fun env => g (f (r env) env) env

 -- Bad attempt
    fun env => bind (f r) g env
    ==>
    fun env => (fun env' => g (f r) env') env
    ==>
    fun env' => g (f r) env'
    ==>
    g (f r) -- Ill-typed! You rewrote wrongly
-/

instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("mod", (· % ·)), ("max", max)]

#eval exampleEnv.lookup "mod" >>= fun f => f 5 2 |> pure

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0 -- In *any* environment, the result is [0]
  | some f => pure (f x y) -- In *any* environment, the result is [f x y]

/- Terrible:
    fun env =>
    let opt := env.lookup op >>= fun f => pure (f x y)
    match opt with
    | none => 0
    | some result => result
 -/
open Special.Prim
#eval Special.evaluateM applyPrimReader
  (prim (other "mod")
    (const 42)
    (prim (other "max")
      (const 3)
      (const 22))) exampleEnv

#eval Special.evaluateM applyPrimReader
  (prim (other "mix")
    (const 1)
    (const 2)) exampleEnv
/-
  For the expression [prim (other "max") (const 1) (const 2)]

  bind (evalM applySp e1) (fun v1 => ...)
  ==>
  fun env => (fun v1 => ...) ((evalM applySp e1) env) env
  ==>
  ...

  [evalM applySp e1] evaluates to the reader that is always 1
  It is applied to [env] which gives you 1 [v1 := 1].
  Then we evaluate [e2], which will give us [v2 := 2].
  Finally we calculate a new reader, using the values of [v1] [v2]
  and [applyPrimReader], which reads the name "max" off of an
  (abstract) environment. It returns the constant reader 0 if
  the name if the lookup fails, otherwise it returns the
  constant reader of the result of the name's implementation
  applied to [v1] and [v2].
-/

end Env

namespace ReaderWithFailure

def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderOption.pure (x : α) : ReaderOption ρ α :=
  fun _ => some x

-- def ReaderOption.bind {α β ρ: Type} (result : ρ → Option α) (next : α → ρ → Option β) : ρ → Option β :=
def ReaderOption.bind
  (result : ReaderOption ρ α)
  (next : α → ReaderOption ρ β) : ReaderOption ρ β :=
  fun env =>
    result env >>= fun x =>
    next x env

/- ~45 min
  [ReaderOption ρ] satisfies the monad contract:

  1.
  bind (pure v) f = f v

  bind (pure v) f
  ===>
  fun env => (pure v) env >>= fun x => f x env
  ===>
  fun env => (fun _ => some v) env >>= fun x => f x env
  ===>
  fun env => some v >>= fun x => f x env
  ===> [Option.some] is a left identity of [>>=]
  fun env => (fun x => f x env) v
  ===>
  fun env => f v env
  ===>
  f v

  2.
  bind v pure = v

  bind v pure
  ==>
  fun env => v env >>= fun x => pure x env
  ==>
  fun env => v env >>= fun x => (fun y => fun _ => some y) x env
  ==>
  fun env => v env >>= fun x => some x
  ==>
  fun env => v env >>= some
  ==> [Option.some] is a right identity of [>>=]
  fun env => v env
  ==>
  v

  3.
  bind (bind v f) g = bind v (fun x => bind (f x) g)

  bind (bind v f) g
  ===>
  fun env => (bind v f) env >>= fun b => g b env
  ===>
  fun env =>
    (fun env' =>
      v env' >>= fun a => f a env') env
    >>= fun b =>
    g b env
  ===>
  fun env =>
    v env   >>= fun a =>
    f a env >>= fun b =>
    g b env

  ###

  bind v (fun x => bind (f x) g)
  ===>
  fun env => v env >>= fun a => (fun x => bind (f x) g) a env
  ===>
  fun env => v env >>= fun a => (bind (f a) g) env
  ===>
  fun env => v env >>= fun a => (
    fun env' => (f a) env' >>= fun b => g b env'
  ) env
  ===>
  fun env =>
    v env   >>= fun a => (
    f a env >>= fun b =>
    g b env)
  ===> [>>=] is associative for the [Option] monad
  fun env =>
    v env   >>= fun a =>
    f a env >>= fun b =>
    g b env

  The three proofs for the [pure] and [bind] operations of [ReaderExcept ε ρ]
  are identical, they follow from the properties of the [Except ε] monad as
  the [ReaderOptions ρ] proofs follow from those of the [Option] monad.

  Qed.
-/
def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α

def ReaderExcept.pure (x : α) : ReaderExcept ε ρ α := fun _ => Except.ok x

def ReaderExcept.bind
  (result : ReaderExcept ε ρ α)
  (next : α → ReaderExcept ε ρ β) : ReaderExcept ε ρ β :=
  fun env =>
    result env >>= fun x =>
    next x env

instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind

instance : Monad (ReaderExcept ε ρ) where
  pure := ReaderExcept.pure
  bind := ReaderExcept.bind

def ReaderOption.read : ReaderOption ρ ρ := fun s => some s
def ReaderOption.fail : ReaderOption ρ α := fun _ => none

def ReaderExcept.read : ReaderExcept ε ρ ρ := fun s => Except.ok s
def ReaderExcept.fail (msg : String) : ReaderExcept String ρ α :=
  fun _ => Except.error msg

open Env in
def applyPrimReaderOption (op : String) (x : Int) (y : Int) :
  ReaderOption Env Int :=
  ReaderOption.read >>= fun env =>
  match env.lookup op with
  | none => ReaderOption.fail
  | some f => ReaderOption.pure (f x y)

open Env in
def applyPrimReaderExcept (op : String) (x : Int) (y : Int)
  : ReaderExcept String Env Int :=
  ReaderExcept.read >>= fun env =>
  match env.lookup op with
  | none => ReaderExcept.fail s!"unknown operator: {op}"
  | some f => ReaderExcept.pure (f x y)

open Special.Prim

def expr : Expr (Special.Prim String) :=
  (prim plus (const 1) (prim (other "mud") (const 42) (const 3)))

#eval Special.evaluateM applyPrimReaderOption expr Env.exampleEnv
#eval Special.evaluateM applyPrimReaderExcept expr Env.exampleEnv

end ReaderWithFailure

namespace Tracing

-- ~45 min
inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α

instance : Monad (Logging.WithLog logged) where
  pure := Logging.ok
  bind := Logging.andThen

open Special Logging in
def applyTraced (op : ToTrace (Prim Empty)) (x : Int) (y : Int) : WithLog (Prim Empty × Int × Int) Int :=
  match op with
  | ToTrace.trace op =>
    save (op, x, y) >>= fun () =>
    Special.applyPrim applyEmpty op x y
    /- I knew I could do without this!
    match op with
    | Prim.plus => ok (x + y)
    | Prim.minus => ok (x - y)
    | Prim.times => ok (x * y) -/

deriving instance Repr for Logging.WithLog
deriving instance Repr for Empty
deriving instance Repr for Special.Prim

open Special.Prim ToTrace
#eval Special.evaluateM applyTraced (
  prim (other (trace times))
    (prim (other (trace plus)) (const 1) (const 2))
    (prim (other (trace minus)) (const 3) (const 4))
  : Expr (Special.Prim (ToTrace (Special.Prim Empty))))

#eval Special.evaluateM applyTraced (
  prim (other (trace times))
    (prim plus (const 1) (const 2))
    (prim minus (const 3) (const 4)))

end Tracing

-- Without effects, calculators would be useless
end ArithExpr

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def firstThirdFifthSeventh' [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

def number' (t : BinTree α) : BinTree (Nat × α) :=
  let rec go (step : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf => (step, leaf)
    | BinTree.branch left v right =>
      let (stepLeft, numberedLeft) := go step left
      let (stepRight, numberedRight) := go (stepLeft+1) right
      (stepRight, branch numberedLeft (stepLeft, v) numberedRight)
  (go 0 t).snd

open Stateful
def number'' (t : BinTree α) : BinTree (Nat × α) :=
  let rec go : BinTree α → State Nat (BinTree (Nat × α))
  | leaf => ok leaf
  | branch left v right =>
    go left ~~> fun numberedLeft =>
    get ~~> fun stepLeft =>
    set (stepLeft+1) ~~> fun () =>
    go right ~~> fun numberedRight =>
    ok (branch numberedLeft (stepLeft, v) numberedRight)
  (go t 0).snd

def number''' (t : BinTree α) : BinTree (Nat × α) :=
  let rec go : BinTree α → State Nat (BinTree (Nat × α))
  | leaf => pure leaf
  | branch left x right => do
    let numberedLeft ← go left
    let n ← get
    set (n + 1)
    let numberedRight ← go right
    pure (branch numberedLeft (n, x) numberedRight)
  (go t 0).snd

#eval number''' aTree

def numberBad (t : BinTree α) : BinTree (Nat × α) :=
  let rec go : BinTree α → State Nat (BinTree (Nat × α))
  | leaf => pure leaf
  | branch left x right => do
    let n ← get
    set (n + 1) -- Updating the state before traversing [left]!
    pure (branch (← go left) (n, x) (← go right))
  (go t 0).snd

#eval numberBad aTree

def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

def number'''' (t : BinTree α) : BinTree (Nat × α) :=
  let rec go : BinTree α → State Nat (BinTree (Nat × α))
  | leaf => pure leaf
  | branch left x right => do
    pure (branch (← go left) ((← increment), x) (← go right))
  (go t 0).snd

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun y =>
    mapM f xs >>= fun ys =>
    pure (y :: ys)

/-
  bind (f x) (fun y =>
  bind (mapM f xs) (fun ys =>
  pure (y :: ys)))
  ===>
  let {log := thisOut, val := thisVal} := f x
  let {log := nextOut, val := nextVal} := (fun y =>
    bind (mapM f xs) (fun ys =>
    pure (y :: ys))) thisVal
  {log := thisOut ++ nextOut, val := nextVal}
  ===>
  let {log := thisOut, val := thisVal} := f x
  let {log := nextOut, val := nextVal} := (fun y =>
    let {log := thisOut, val := thisVal} := mapM f xs
    let {log := nextOut, val := nextVal} := (fun ys =>
      pure (y :: ys)) thisVal
    {log := thisOut ++ nextOut, val := nextVal}) thisVal
  {log := thisOut ++ nextOut, val := nextVal}

  After a number of steps, [f x] will be replaced for [thisOut]
  and the list generated by [mapM f xs] will be replaced for
  [nextOut]. [f x] will come first in the output log.

  It is easy to see that if the order of the bind operations is
  swapped, the elements will be logged in reverse order.
-/

def mapM' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← mapM f xs
    pure (y :: ys)

-- Using nested actions
def mapM'' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do pure ((← f x) :: (← mapM f xs))

open Logging in
def logAnything (x : α) : WithLog α α := do
  save x
  pure x

#eval mapM logAnything [1,2,3,4,5]
#eval mapM' logAnything [1,2,3,4,5]
#eval mapM'' logAnything [1,2,3,4,5]

namespace EvalWithDo

open ArithExpr
open ArithExpr.Special

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) (op : Prim special) (x : Int) (y : Int) : m Int :=
  match op with
  | Prim.plus => pure (x + y)
  | Prim.minus => pure (x - y)
  | Prim.times => pure (x * y)
  | Prim.other sp => applySpecial sp x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim op e1 e2 => do
    applyPrim applySpecial op
      (← evaluateM applySpecial e1)
      (← evaluateM applySpecial e2)

-- Just doing one use case for now
open ArithExpr
open Tracing Special Logging
def applyTraced (op : ToTrace (Prim Empty)) (x : Int) (y : Int) : WithLog (Prim Empty × Int × Int) Int :=
  match op with
  | ToTrace.trace op' => do
    save (op', x, y)
    applyPrim applyEmpty op' x y

open Special.Prim ToTrace Prim Expr
#eval evaluateM applyTraced (
  prim (other (trace times))
    (prim (other (trace plus)) (const 1) (const 2))
    (prim (other (trace minus)) (const 3) (const 4))
  : Expr (Special.Prim (ToTrace (Special.Prim Empty))))
end EvalWithDo

def firstThirdFifthSeventh''' [Monad m] (lookup : List α → Nat → m α) (l : List α) : m (α × α × α × α) := do
  pure ((← lookup l 0),
        (← lookup l 2),
        (← lookup l 4),
        (← lookup l 6)) -- ✨magic✨

def mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

def BinTree.mirror : BinTree α → BinTree α
  | leaf => leaf
  | branch l x r => branch (mirror r) x (mirror l)

def BinTree.empty : BinTree α := .leaf

#check empty
#check .empty
#check (empty : BinTree Nat)
#check (.empty : BinTree Nat)

inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr

def Weekday.isWeekend : Weekday → Bool
  | saturday | sunday => true
  | _ => false

-- A sum type of homogenous values can be condensed
def condense : α ⊕ α → α
  | .inl x | .inr x => x

-- Variables bound by the patterns need not have the same type
def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"

#eval stringy (.inl 0)
#eval stringy (.inr .saturday)

set_option linter.unusedVariables false

def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => n

def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
  | .inl (n, x) | .inr (n, x) => x

def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str -- [str] is defined in both cases. The global definition is used as fallback

#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × Unit))
#eval getTheString (.inr (20, "twenty"))
