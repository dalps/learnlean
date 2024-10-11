def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

#eval woodlandCritters[0]
#eval woodlandCritters[1]
#eval woodlandCritters[2]?
#eval woodlandCritters[3]?
#eval woodlandCritters[3]!
-- #eval woodlandCritters[3]

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

/-- [Prop] is a supertype containing all propositions.
    Proposition themselves are types.
    [=] (or [Eq]) is a proposition.
-/
def OnePlusOneIsTwo' : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo' : OnePlusOneIsTwo' := rfl

theorem onePlusOneIsTwo'' : 1 + 1 = 2 := by
  simp

theorem addAndAppend : 1 + 1 = 2 /\ "Str".append "ing" = "String" := And.intro rfl rfl

-- Another snippet that doesn't work :(
theorem addAndAppend' : 1 + 1 = 2 /\ "Str".append "ing" = "String" := by simp! -- works with [!]

theorem andImpliesOr : A /\ B → A \/ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by simp
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by simp
theorem trueIsTrue : True := True.intro
theorem trueOrFalse : True ∨ False := by simp
theorem falseImpliesTrue : False → True :=
  fun _ => True.intro -- anything implies [True]

/- Propositions let us safely access a list in a function
   that would otherwise not be safe. -/
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

/- A caller of [third] must provide evidence that [xs]
   has at least three elements. -/
#eval woodlandCritters.length
#eval third woodlandCritters (by simp!)

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters
#eval thirdOption ["foo", "bar"]

#eval woodlandCritters[1]!
-- #eval ([] : List Nat)[1]! -- crashes Lean server

/- [xs[2]!] is not allowed to crash, because there's no
   guarantee [α] is not empty. Like infinite loops, crashing
   could allow the empty type to be inhabited
   and therefore [False] would become provable. -/
def unsafeThird (xs : List α) : α := xs[2]!

def exercise1_1 : 2 + 3 = 5 := rfl
def exercise1_2 : 15 - 8 = 7 := rfl
def exercise1_3 : "Hello, ".append "world" = "Hello, world" := rfl
-- def exercise1_4 : 5 < 18 := rfl -- [rfl] doesn't handle inequalities

def exercise2_1 : 2 + 3 = 5 := by simp
def exercise2_2 : 15 - 8 = 7 := by simp
def exercise2_3 : "Hello, ".append "world" = "Hello, world" := by simp!
def exercise2_4 : 5 < 18 := by simp

def fifth (xs : List α) (ok : 4 < xs.length) : α := xs[4]

#eval fifth [1,3,5,7,9] (by simp)
