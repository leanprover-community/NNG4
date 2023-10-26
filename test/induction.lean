import Game.Tactic.Induction
import Game.MyNat.Addition
import Mathlib.Tactic.Have
import Mathlib.Tactic

example (a b : ℕ) : a + b = a → b = 0 := by
  induction b with d hd
  -- looks great
  -- base case
  /-
  a : ℕ
  ⊢ a + 0 = a → 0 = 0
  -/
  sorry; sorry

example (a b c : ℕ) (g : c = 0) : a + b = a → b = 0 := by
  intro h -- h : a + b = a
  induction b with d hd generalizing g
  -- aargh
  -- base case
  /-
  a b: ℕ
  h✝ : a + b = a
  h : a + 0 = a
  ⊢ 0 = 0
  -/
  -- Why does b still exist in the base case? And why does h✝ exist at all?
  sorry; sorry
