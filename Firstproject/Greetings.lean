def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "你好！"
  englishGreeting

/-
  ===> denotes normal steps
  =!=> denotes effectful steps
  ###

  |- main

  ===> Evaluation of [main]
  |- do
    let englishGreeting := IO.println "Hello!"
    IO.println "你好！"
    englishGreeting

  ===> [IO.println "Hello!"] is evaluated to a [IO Unit] and bound to [englishGreeting]
  (englishGreeting := IO.println "Hello!") |-
    do
      IO.println "你好！"
      englishGreeting

  =!=> (>> 你好！) -- [IO.println "你好！"] is evaluated to an [IO Unit] and executed immediately after
  (englishGreeting := IO.println "Hello!") |-
    do
      englishGreeting

  ===> Evaluation of a name
  (englishGreeting := IO.println "Hello!") |-
    do
      IO.println "Hello!"

  =!=> (>> Hello!) Evaluation + execution of an [IO Unit] action
 -/
