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

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α -> α -> BinTree α -> BinTree α
deriving Repr

def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l v r =>
    let (nodesL, sumL) := inorderSum l
    let (hereVisited, hereSum) := ([v], v)
    let (nodesR, sumR) := inorderSum r
    (nodesL ++ hereVisited ++ nodesR, sumL + hereSum + sumR)

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

-- ## Stateful computations

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

end Logging


-- Use a single element to represent the one element word
instance : Coe α (List α) where
  coe a := [a]

example : Option Nat := List.get? (1 : Nat) 42
example : Option Char := List.get? 'a' 42
example : Option Bool := List.get? true 0
