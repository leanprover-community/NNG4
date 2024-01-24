import Game.Levels.Addition
import Game.MyNat.Multiplication

World "Multiplication"
Level 1
Title "mul_one"

namespace MyNat

Introduction
"

See the new \"*\" tab in your lemmas, containing `mul_zero` and `mul_succ`.
Right now these are the only facts we know about multiplication.
Let's prove nine more.

Let's start with a warm-up: no induction needed for this one,
because we know `1` is a successor.
"

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

TheoremDoc MyNat.mul_zero as "mul_zero" in "*"
"
`mul_zero m` is the proof that `m * 0 = 0`."

TheoremDoc MyNat.mul_succ as "mul_succ" in "*"
"
`mul_succ a b` is the proof that `a * succ b = a * b + a`.
"

NewLemma MyNat.mul_zero MyNat.mul_succ

TheoremDoc MyNat.mul_one as "mul_one" in "*" "
`mul_one m` is the proof that `m * 1 = m`.
"

/-- For any natural number $m$, we have $ m \times 1 = m$. -/
Statement mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]
  rfl

TheoremTab "*"
