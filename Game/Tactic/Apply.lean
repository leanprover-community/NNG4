import Mathlib.Tactic.Replace

open Lean Elab Tactic

/--
If `(h : A)` is a proof of `A` and `f : A → B` an implication then
`apply f at h` turns `h` into a proof of `B`.

This is a game-specific implementation and not an official Lean tactic.
It is equivalent to the tactic `replace h := f h`.
-/
syntax (name := applyAt) "apply" ident " at " ident : tactic

elab_rules : tactic | `(tactic| apply $thm at $hyp) => do
  evalTactic (← `(tactic| replace $hyp := $thm $hyp))

-- Test
example (A B C : Prop) (ha : A) (f : A → B) (g : B → C) : C := by
  apply f at ha
  apply g at ha
  exact ha
