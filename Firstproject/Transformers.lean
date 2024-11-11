-- Monad transformers are transfrormes for type transformers

/- We've already went over [ReaderT], which wraps a monad in an environment-accepting function. -/
#check MonadWithReaderOf

/- [OptionT], the monad transformer for nullable types, makes the monad's results optional by sneaking in [Option] -/
def OptionT' (m : Type u → Type v) (α : Type u) : Type v :=
  m (Option α)

-- IO actions that may not return a value
#check OptionT IO

-- IO actions that may not return a string
#check OptionT IO String

def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trim
  if trimmed.isEmpty then
    OptionT.fail -- [failure] works too
  else
    pure trimmed

structure UserInfo where
  name : String
  favoriteBeetle : String

/- This procedure mixes the monads [IO] and [OptionT IO] in the same do-block.
  The type of the whole do-block is [OptionT IO], as the signature reports.
  This intermingle wouldn't be possible without the instance of [MonadLift]
  for [OptionT m] readily defined by the standard library.
-/
def getUserInfo : OptionT IO UserInfo := do
  let stdout ← IO.getStdout
  stdout.putStrLn "Come ti chiami?"
  let name ← getSomeInput
  stdout.putStrLn "Qual è il tuo coleottero preferito?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩

/- And now we use [OptionT IO] in a purely [IO] context to act upon the
  presence of input or lack thereof -/
def interact : IO Unit := do
  match ← getUserInfo with -- using [OptionT IO]
  | none => IO.eprintln "What!?"
  | some cretin => IO.print s!"This bloke called {cretin.name} is keen on
  {cretin.favoriteBeetle}"

#eval interact

instance [Monad m] : Monad (OptionT m) where
  pure x := pure (some x) -- The monad contains the option: we want [pure] from the interface of the underlying [m]
  bind x next :=
    x >>= fun opt => -- Lean believes we're using [bind] from the [Option] instance: it expects a non-optional [α] in [opt]
    match opt with
    | none => pure none -- Lean's believes we're using [pure] from [Option], i.e. it's selecting the wrong monad instance
    | some v => next v

/- Type annotiation help it figure out the right instance, but they are too noisy -/
instance [Monad m] : Monad (OptionT m) where
  pure {α : Type} (x : α) : (m (Option α)) := pure (some x)
  bind {α β : Type} (x : m (Option α)) (next : α → m (Option β)) : m (Option β) :=
    x >>= fun opt =>
    match opt with
    | none => pure none
    | some v => next v

-- Ascriptions look a lot nicer
instance [Monad m] : Monad (OptionT m) where
  pure x := (pure (some x) : m (Option _))
  bind x next :=
    (x >>= fun opt =>
    match opt with
    | none => pure none
    | some v => next v : m (Option _))

/- But there's a better solution: guiding the instance search to the correct instances right from the signature!

  The following two helpers return their input unchanged, but their types are key: they set the boundary between code that intends to use the interface of [OptionT] ([run]) and code intends to use the interface of the underlying monad [m] ([mk]).
  Both of them rely on the direct definition [OptionT], which
  smudged such boundary enough for type search to fail.
-/

def OptionT'.mk (x : m (Option α)) : OptionT m α := x

def OptionT'.run (x : OptionT' m α) : m (Option α) := x

/-
  In the definition of the [Monad] instance for [OptionT] we can point instance search to the interface of [m] (rather than the incorrect instance of [Monad Option]) by using [OptionT.mk].
-/
instance [Monad m] : Monad (OptionT' m) where
  pure x := OptionT'.mk $ pure (some x)
  bind action next := OptionT'.mk $ do -- [$] not necessary
    match ← action with
    | none => pure none
    | some v => next v

/- Does the new instance satisfy the monad contract?

  1. bind (pure v) f = f v

  bind (pure v) f
  ={ unfold bind }=>
  bindM (pure v) fun o =>
  match o with
  | none => pureM none
  | some x => f x
  ={ unfold pure }=>
  bindM (pureM (some v)) fun o =>
  match o with
  | none => pureM none
  | some x => f x
  ={ pureM is a left identity of bindM }=>
  match some v with
  | ... => ...
  | some x => f x
  ===>
  f v

  2. bind v pure = v

  bind v pure
  ={ unfold bind }=>
  bindM v fun o =>
  match o with
  | none => pureM none
  | some x => pure x
  ={ unfold pure }=>
  bindM v fun o =>
  match o with
  | none => pureM none
  | some x => pureM (some x)
  ===>
  bindM v (fun o => pureM o)
  ===>
  bindM v pureM
  ={ pureM is a right identity of bindM }=>
  v

  3. x >>= f >>= g = x >>= (fun y => f y >>= g)

  bind (bind x f) g
  ={ unfold outer bind }=>
  bindM (bind x f) fun z =>
  match z with
  | none => pureM none
  | some v => g v
  ={ unfold bind }=>
  bindM (
    bindM x fun y =>
    match y with
    | none => pureM none
    | some w => f w
  ) fun z =>
  match z with
  | none => pureM none
  | some v => g v
  ={ rewrite using infix operators }=>
   (x >>=M fun y =>
   match y with
   | none => pureM none
   | some w => f w)
  >>=M fun z =>
  match z with
  | none => pureM none
  | some v => g v
  ={ associativity of bindM }=>
  x >>=M fun y =>
  (match y with
  | none => pureM none
  | some w => f w) >>=M fun z =>
  match z with
  | none => pureM none
  | some v => g v
  ={ safe to remove parentheses }=>
  x >>=M fun y =>
  match y with
  | none => pureM none
  | some w =>
    f w >>=M fun z =>
    match z with
    | none => pureM none
    | some v => g v


  x >>= (fun y => f y >>= g)
  ===>
  x >>=M fun z =>
  match z with
  | none => pureM none
  | some v => (fun y => f y >>= g) v
  ===>
  x >>=M fun z =>
  match z with
  | none => pureM none
  | some v => (fun y =>
    f y >>=M fun a =>
    match a with
    | none => pureM none
    | some w => g w) v
  ===>
  x >>=M fun z =>
  match z with
  | none => pureM none
  | some v =>
    f v >>=M fun a =>
    match a with
    | none => pureM none
    | some w => g w

  Qed. (33:58 min all three)
-/

-- The [OptionT] transformer also lends itself nicely to an [Alternative] instance. With the concept of failure the having been introduced in the monad [OptionT m], the [orElse] method is useful for selecting the first successful result from a number of subprograms in [m]:
instance [Monad m] : Alternative (OptionT' m) where
  failure := OptionT'.mk $ pure none
  orElse a b := OptionT'.mk do
  match ← a with
  | none => b ()
  | some v => pure (some v)

/- Lifting [m] to [OptionT] is a piece of cake: it suffices to wrap [some] around the result of a computation of [m].
-/
instance [Monad m] : MonadLift m (OptionT' m) where
  monadLift m := OptionT'.mk $ bind m (fun x => pure (some x))
  -- OptionT'.mk do pure (some (← m))
  -- OptionT'.mk $ some <$> m

-- # Exception transformer

def ExceptT' (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)

/- The following helper function guide the typecheck towards the
  correct [Monad] instances. This time there's the additional subtlety that the typo of errors and result must belong to the same universe level. Otherwise, Lean would infer a more general type signature where they can take on distinct levels. Since their values become eventually arguments to [m], we want both of these types to be on the same universe level as [m]. -/

def ExceptT'.mk {ε α : Type u} (x : m (Except ε α)) : ExceptT' ε m α := x
def ExceptT'.run {ε α : Type u} (x : ExceptT' ε m α) : m (Except ε α) := x

/- The [Monad] instance is identical to that of [OptionT],
  except it propagates a specific error value in place of the generic [none].

  Needless to say the proofs of the contract are also identical.
-/
instance [Monad m] : Monad (ExceptT' ε m) where
  pure x := ExceptT'.mk (pure (.ok x))
  bind action next := ExceptT'.mk do
    match ← action with
    | .ok result => next result
    | .error err => pure (.error err)

/- Unlike [OptionT], [ExceptT] opens up new lifting opportunities besides [m] to [ExceptT ε m].

  It makes sense to add the exceptions provided by an
  [Except ε] monad to another monad [m].
-/
instance [Monad m] : MonadLift (Except ε) (ExceptT' ε m) where
  monadLift exn := ExceptT'.mk $ pure exn

/- On the other hand, the actions of [m] _map_ to successful
  instances of [Except], which translates to wrapping [.ok] around [m]'s action.
-/
instance [Monad m] : MonadLift m (ExceptT' ε m) where
  monadLift action := ExceptT'.mk $ .ok <$> action
  -- ExceptT'.mk do pure (.ok (← action))

/- A monad that implements [MonadExcept] can thrown and recover from exception of any type: -/

inductive Err where
  | badInput : String → Err
  | divByZero

def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0 then
    throw Err.divByZero
  else
    pure (n / k)

def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none => throw $ .badInput s
  | some n => pure n

def divFrontend' [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  tryCatch (do
    pure (toString (← divBackend (← asNumber n) (← asNumber k)))
  ) (fun -- [fun] straight up opens a pattern match
  | .badInput s => pure s!"\"{s}\" is not a number!"
  | .divByZero => pure s!"Tried to divide {k} by {n}!" -- By the time this is thrown [k] and [n] are guaranteed to represent numbers
  )

def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  try
    pure $ toString (← divBackend (← asNumber n) (← asNumber k))
  catch
  | .badInput s => pure s!"\"{s}\" is not a number!"
  | .divByZero => pure s!"Tried to divide {n} by zero!"

/- Note: an instance of [MonadExcept] for [Except] is predefined by the standard library, meaning [throw] and [try ... catch ...] are available for use within a [Except] computation without additional code! -/
instance : MonadExcept Err (Except Err) where
  throw e := .error e
  tryCatch action handler :=
    match action with
    | .error e => handler e
    | .ok v => .ok v

deriving instance Repr for Err

#check (divFrontend "9" "2" : Except Err String)
#eval (divFrontend "9" "2" : Except Err String)
#eval (divFrontend "foo" "2" : Except Err String)
#eval (divFrontend "2" "0" : Except Err String)

-- # State transformer

def StateT' (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

/- A monad transformed by [StateT] is still a monad abiding by the monad contract (prove it!) -/
instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (x, s') ← result s
    next x s'

/-
  The [StateT] type class provides [get] and [set] methods implemented by means of functions.

  One must be prudent when using [set]:
-/
namespace CountDiacritics

structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive Err where
  | notALetter : Char → Err
deriving Repr

#eval "hello".toUpper

def vowels :=
  let lowerVowels := "aeiouy"
  lowerVowels ++ lowerVowels.toUpper

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.toUpper

#eval vowels
#eval consonants
#check set

def countLettersR (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop : List Char → StateT LetterCounts (Except Err) Unit
  | [] => pure ()
  | c :: chars => do
      loop chars
      let counts ← get
      if c ∈ vowels.data then
        set {counts with vowels := counts.vowels + 1}
      else if c ∈ consonants.data then
        set {counts with consonants := counts.consonants + 1}
      else
        throw (.notALetter c)
  loop str.data

#eval 'è'.isAlpha
-- The book code assumes [isAlpha] is true on diacritics, which is not the case...

def countLettersL (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop : List Char → StateT LetterCounts (Except Err) Unit
  | [] => pure ()
  | c :: chars => do
      let counts ← get
      if c.isAlpha then
        if c ∈ vowels.data then
          set {counts with vowels := counts.vowels + 1}
        else if c ∈ consonants.data then
          set {counts with consonants := counts.consonants + 1}
        else
          pure ()
      else
        throw (.notALetter c)
      loop chars
  loop str.data

#eval (countLettersL "ABcdEFgh") ⟨0,0⟩
#eval (countLettersL "ABcdE1gh") ⟨0,0⟩
#eval (countLettersL "àBcdE1gh") ⟨0,0⟩
#eval (countLettersR "àBcdE1gh") ⟨0,0⟩
#eval (countLettersL "éBcdègh") ⟨0,0⟩
-- 24:45 min (weak!) - wrong: it should *not* throw an error on diacritics!

/- The state updates can be made considerably more robust by using the [modify] helper. It streamlines the process of retrieving the state with [get], updating it and setting it with [set]. -/

#check modify

def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop : List Char → StateT LetterCounts (Except Err) Unit
  | [] => pure ()
  | c :: chars => do
      if c.isAlpha then
        if c ∈ vowels.data then
          modify fun st => {st with vowels := st.vowels + 1}
        else if c ∈ consonants.data then
          modify fun st => {st with consonants := st.consonants + 1}
        else
          pure ()
      else
        throw (.notALetter c)
      loop chars
  loop str.data

#eval (countLettersL "ABcdEFgh") ⟨0,0⟩
#eval (countLettersL "ABcdE1gh") ⟨0,0⟩
#eval (countLettersL "àBcdE1gh") ⟨0,0⟩
#eval (countLettersR "àBcdE1gh") ⟨0,0⟩
#eval (countLettersL "éBcdègh") ⟨0,0⟩

/- Note: [modify] relies on an instance of [MonadState],
  which we never instantiated. This means that Lean
  automatically defines such instance for monads built
  with [StateT]! How cool is that?

  The operations on states [get], [set], [modify] and [modifyGet] are methods of the [MonadState] type class.

  Behind the scenes, [modify] is a specialized version of another function called [modifyGet] that accepts a function that computes both a return value and a state.
  [modify] simply twists the return value to a vacuous [unit] in a default method definition.
-/

#check MonadState

/- What if an instance of [MonadState] exists for two different types of states?
  Lean will fail to infer the correct instance when the two are intermingled in
  the same [do]-block.

  The solution is to remove the [outParam] directive to the type of the state and let the user provide it explicitly when callding the [MonadState] methods, through a type argument. This is accomplished by the [MonadStateOf] type class, and, generally speaking, by the **Of** version of any transformer.

  It turns out [MonadState] is defined in temrs of its [Of] version. All non-[Of] transformers type classes are defined in terms of their [Of] version. This means that implementing the [Of] version yields implementations of both at no additional effort.

  The methods of the [Of] version all end with the article "The", hinting at the fact that they expect a type argument.
-/
#check MonadStateOf

end CountDiacritics

-- # Id

/- The identity monad [Id] is also an identity for transformers.
  Recall that [Id] is the monad with no effects at all.
  For instance, [StateT σ Id] works just like [State σ]: by adding state effects to no effects at all, we get state effects. Easy enough.
-/

instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (x, s') ← result s
    next x s'

#check LawfulMonad
/-
  [Monad (StateT σ m)] satisfies the monad contract for any monad [m].

  1. bind (pure x) f = f x - 5:16 min

  bind (pure x) f
  ={ unfold [bind] }=>
  fun s =>
    (pure x) s >>=M fun (v, s') =>
    f v s'
  ={ unfold [pure x] }=>
  fun s =>
    (fun r => pureM (x,r)) s >>=M fun (v, s') =>
    f v s'
  ={ simplify }=>
  fun s =>
    pureM (x,s) >>=M fun (v,s') =>
    f v s'
  ={ pureM is a left identity of >>=M }=>
  fun s =>
    f x s
  ={ simplify }=>
  f x


  2. bind x pure = x - 11:34 min

  bind x pure
  ={ unfold [bind] }=>
  fun s =>
    x s >>=M fun (v, s') =>
    pure v s'
  ={ unfold [pure v] }=>
  fun s =>
    x s >>=M fun (v, s') =>
    (fun r => pureM (v, r)) s'
  ={ simplify }=>
  fun s =>
    x s >>=M fun (v, s') =>
    pureM (v, s')
  ={ simplify }=>
  fun s =>
    x s >>=M pureM
  ={ [pureM] is a right identity of [>>=M] }=>
  fun s => x s
  ={ simplify }=>
  x


  3. x >>= f >>= g = x >>= (fun x => f x >>= g)

  x >>= f >>= g
  ===>
  bind (bind x f) g
  ={ unfold bind }=>
  bind (fun s =>
    x s >>=M fun (v, s') =>
    f v s') g
  ={ unfold bind }=>
  fun r =>
    (fun s =>
      x s >>=M fun (v, s') =>
      f v s') r >>=M fun (w, r') =>
    g w r'
  ={ simplify }=>
  fun r =>
    (x r >>=M fun (v, s')) =>
    f v s' >>=M fun (w, r') =>
    g w r'
  ={ associativity of >>=M }=>
  fun r =>
    x r >>=M fun (v, s') =>
    f v s' >>=M fun (w, r') =>
    g w r'


  x >>= (fun x => f x >>= g) - 23:08 min
  ===>
  bind x (fun x => bind (f x) g)
  ={ unfold bind }=>
  bind x (fun y =>
    fun s =>
      (f y) s >>=M fun (v, s') =>
      g v s')
  ={ unfold bind }=>
  fun r =>
    x r >>=M fun (w, r') =>
    (fun y =>
      fun s =>
        (f y) s >>=M fun (v, s') =>
        g v s') w r'
  ={ simplify }=>
  fun r =>
    x r >>=M fun (w, r') =>
    f w r' >>=M fun (v, s') =>
    g v s'
  ={ rename binders }=>
  fun r =>
    x r >>=M fun (v, s') =>
    f v s' >>=M fun (w, r') =>
    g w r'

  Qed.

  I am *not* doing the proof of [ExceptT], it has the same shape of [OptionT]'s.
-/

structure WithLog (logged : Type u) (α : Type v) : Type (max u v) where
  log : List logged
  val : α
deriving Repr

def WithLog.andThen (result : WithLog Λ α) (next : α → WithLog Λ β) : WithLog Λ β :=
  let {log := thisOut, val := thisVal} := result
  let {log := nextOut, val := nextVal} := next thisVal
  {log := thisOut ++ nextOut, val := nextVal}

def WithLog.ok (x : β) : WithLog α β := {log := [], val := x}

def WithLog.save (data : α) : WithLog α Unit := {log := [data], val := ()}

/- Wrong way around - the [WithLog] should be inside the monad

def WithLogT (logged : Type u) (m : Type u → Type v) (α : Type u) :=
  WithLog logged (m α)
-/

def WithLogT (logged : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (WithLog logged α)

-- Wasted 20 min forgetting [logged] and [α] had to be on the same level :/
def WithLogT.mk {logged α : Type u} (x :  m (WithLog logged α)) : WithLogT logged m α := x

def WithLogT.run {logged α : Type u} (x : WithLogT logged m α) : m (WithLog logged α) := x

instance [Monad m] : Monad (WithLogT logged m) where
  pure x := WithLogT.mk $ pure (.ok x)
  bind x f := WithLogT.mk $ do
    let {log := thisLog, val := thisVal} := (← x)
    let {log := nextLog, val := nextVal} := (← f thisVal)
    pure {log := thisLog ++ nextLog, val := nextVal}

#check MonadWithReaderOf
#check MonadExceptOf

class MonadWithLog (logged : outParam (Type u)) (m : Type u → Type v) : Type (max u v) where
  save : logged → m PUnit

instance [WithLogT logged m] : MonadWithLog logged m where
-- Trace arithmetic expression with division

inductive ArithException where
  | divisionByZero

inductive Prim where
  | add
  | sub
  | mul
  | div

inductive ArithExpr where
  | const : Nat → ArithExpr
  | prim : Prim → ArithExpr → ArithExpr → ArithExpr

def eval : ArithExpr → WithLogT (Prim × Nat × Nat) (Except ArithException) Nat
  | .const n => pure n
  | .prim op e1 e2 => do
    .save
