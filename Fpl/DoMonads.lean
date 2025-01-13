def firstThirdFifthSeventh' [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

#print Nat
#print Char.isAlpha
#print List.lookup
#print List.isEmpty
-- Remember: a monad is a type function
#print IO -- Defined as [EIO IO.error]
/-
  [EIO IO.error α] is the type of IO actions that will
  either terminate with an error of type
  [IO.error] or succeed with a value of type [α]. -/
#print IO.Error
#print EIO -- Uses [IO.RealWorld] as state, leaves [ε] and [α] abstract
-- [EStateM] is a monad that tracks error and state at the same time
#print EStateM
#print EStateM.Result
#print EStateM.pure
-- [EStateM.bind] combines [Except.bind] and [State.bind]
#print EStateM.bind
/- Given an IO action [x], [bind] passes the modified world [s] to a new action built with [f] -/
#print IO.RealWorld -- Confused, baffled
#print Unit
#print PUnit
