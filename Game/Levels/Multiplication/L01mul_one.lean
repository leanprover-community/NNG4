import Game.Levels.Addition.L05add_right_comm
import Game.MyNat.Multiplication

World "Multiplication"
Level 1
Title "mul_one"

open MyNat

Introduction
"

See the new \"Mul\" tab in your lemmas, containing `mul_zero` and `mul_succ`.

Let's start with a warm-up: no induction needed for this one,
because we know `1` is a successor.
"

LemmaDoc MyNat.mul_one as "mul_one" in "Mul" "foobar"

/-- For any natural number $m$, we have $ m \\cdot 1 = m$. -/
Statement MyNat.mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]
  rfl

LemmaDoc MyNat.mul_zero as "mul_zero" in "Mul"
"hi"
LemmaDoc MyNat.mul_succ as "mul_succ" in "Mul"
"hithere"
NewLemma MyNat.mul_zero MyNat.mul_succ

DefinitionDoc Mul as "*" "
  `Mul a b`, with notation `a * b`, is the usual
  product of natural numbers. Internally it is
  via two axioms:

  * `mul_zero a : a * 0 = 0`

  * `mul_succ a b : a * succ b = a * b + a`

Other theorems about naturals, such as `zero_mul`,
are proved by induction from these two basic theorems.
"

NewDefinition Mul

LemmaTab "Mul"
