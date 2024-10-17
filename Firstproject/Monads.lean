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

namespace Handling

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

def andThen (e : Except ε α) (next : α -> Except ε β) : Except ε β :=
  match e with
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

end Handling

namespace Logging

end Logging
