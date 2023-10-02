import Mathlib.Tactic.Replace
import Std -- TODO: This is mathlib4#7080

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

-- failing test
example (h1 : ∀ x, Nat.succ x = 4 → x = 3) (a : Nat) (h : Nat.succ a = 4) : a = 3 := by
  -- apply h1 at h -- fails
  replace h := h1 _ h -- works
  exact h
