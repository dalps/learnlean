inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

instance : Coe α (Many α) where
  coe := Many.one

def Many.union : Many α → Many α → Many α
  | none, m => m
  | more one others, m => more one (fun () => (others ()).union m)

def Many.fromList : List α → Many α
  | [] => none
  | x :: xs => Many.more x (fun () => fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, none => []
  | n + 1, more x xs => x :: ((xs ()).take n)

def Many.takeAll : Many α → List α
  | none => []
  | more x xs =>  x :: (xs ()).takeAll

instance [ToString α] : ToString (Many α) where
  toString xs := xs.takeAll.toString

def Many.pure : α → Many α := Many.one

def Many.bind : Many α → (α → Many β) → Many β
  | none, _ => none -- Nothing to combine, return nothing
  | more x xs, next =>
    Many.union (next x) (bind (xs ()) next)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

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
