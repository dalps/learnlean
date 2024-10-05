-- The [do] syntax models imperative programs
def main : IO Unit := do
  let stdin ← IO.getStdin -- Initializing an IO variable through an IO action
  let stdout ← IO.getStdout

  /- IO expression.
    Does not introduce new varialbes. Its execution
    proceeds in two separate phases: first it is
    evaluated by applying the [putStrLn] function to
    [stdout] and the string to yield a value. This
    value has type [IO Unit]. Values of such type are
    called _IO actions_ and they can be _executed_. In this
    instance, executing the IO action writes the string
    to the output stream. -/
  stdout.putStrLn "你叫什么名字？"
  /- The result of this IO expression is an [IO String] value.
    This time, the type tells us that its execution (if successful)
    isn't void, but it returns a string value corresponding to the
    user's input. We retrieve this string and binds it to the [input] variable. -/
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace -- Only evaluation

  /- Another IO expression. It is first evaluated to
    an IO action whose execution to prints the given string. -/
  stdout.putStrLn s!"你好，{name}!"

#check main
#eval main

#eval "Hello!!!".dropRightWhile (· == '!')
#eval "Hello123".dropRightWhile (¬ ·.isAlpha)


/- Functions are control structures -/

/- [twice a] returns an IO action that will execute [a] twice.
  Note: it does not run itself the action. -/
def twice (action : IO Unit) : IO Unit := do
  action
  action

#eval twice (IO.println "shy") -- [do] not necessary for a single IO expression

#eval do
  twice (IO.println "shy")
  twice (IO.println "shy")

def nTimes (action : IO Unit) : Nat -> IO Unit
  | 0 => pure ()
  | n + 1 => do
              action
              nTimes action n

#eval nTimes (IO.println "kero") 3

/- IO actions are first-class values.
   As such, they can be "freezed" in data structures for latex execution. -/

def countdown : Nat -> List (IO Unit)
  | 0 => [IO.println "TIMMY!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 := countdown 5

#eval (countdown 5).length
#eval from5.length

/- [runActions] reduces a list of actions to a single action that runs
  each action of the list in sequence. -/
def runActions : List (IO Unit) -> IO Unit
  | [] => pure ()
  | a :: actions => do a; runActions actions

#eval runActions from5

-- [do] blocks intercalate evaluation and execution
