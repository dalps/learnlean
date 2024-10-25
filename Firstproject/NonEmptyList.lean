structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

def NonEmptyList.get? : NonEmptyList α -> Nat -> Option α
  | xs, 0 => some xs.head
  | { head := _, tail := xs }, n + 1 => xs.get? n

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i <= xs.tail.length

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]'ok

instance {α : Type} : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

@[default_instance]
instance : Append (NonEmptyList α) where
  append a b := ⟨a.head, a.tail ++ b.head :: b.tail⟩

instance : CoeDep (List α) (a :: as) (NonEmptyList α) where
  coe := ⟨a,as⟩
