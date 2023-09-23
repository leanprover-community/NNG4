import Game.Levels.Addition.L05add_right_comm
import Game.MyNat.Multiplication

World "Multiplication"
Level 1
Title "mul_one"

open MyNat

Introduction
"
Let's start with an easy one: no induction needed. Your two new theorems
are `mul_zero` and `mul_succ`; click on their names on the right in the
\"Multiplication\" tab **TODO** what tab?

As a side note, the lemmas about addition are still available in your inventory
in the lemma tab \"Add\" while the new lemmas about multiplication appear in the
tab \"Mul\".
"

/-- For any natural number $m$, we have $ m \\cdot 1 = m$. -/
Statement MyNat.mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]
  rfl

LemmaTab "Mul"
