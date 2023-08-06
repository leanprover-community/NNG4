import Mathlib.Tactic.Replace

open Lean Elab Tactic

/--
If `(h : A)` is a proof of `A` and `f : A → B` an implication then
`apply f to h` turns `h` into a proof of `B`.

This is a game specific implementation. It is equivalent to the
tactic `replace h := f h`.
-/
syntax (name := applyTo) "apply" ident " to " ident : tactic

elab_rules : tactic | `(tactic| apply $thm to $hyp) => do
  evalTactic (← `(tactic| replace $hyp := $thm $hyp))

-- Test
example (A B C : Prop) (ha : A) (f : A → B) (g : B → C) : C := by
  apply g
  apply f to ha
  assumption
