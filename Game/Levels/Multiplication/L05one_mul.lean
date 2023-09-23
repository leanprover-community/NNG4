import Game.Levels.Multiplication.L04mul_comm

World "Multiplication"
Level 5
Title "one_mul"

namespace MyNat

Introduction
"
These proofs from addition world might be useful here:

* `one_eq_succ_zero : 1 = succ 0`
* `succ_eq_add_one a : succ a = a + 1`

We just proved `mul_one`, now let's prove `one_mul`.
Then we will have proved, in fancy terms,
that 1 is a \"left and right identity\"
for multiplication (just like we showed that
0 is a left and right identity for addition
with `add_zero` and `zero_add`).
"

/-- For any natural number $m$, we have $ 1 \\cdot m = m$. -/
Statement one_mul
    (m : ℕ): 1 * m = m := by
  induction m with d hd
  · rw [mul_zero]
    rfl
  · rw [mul_succ]
    rw [hd]
    have := succ_eq_add_one
    rw [succ_eq_add_one]
    rfl

LemmaTab "Mul"

Conclusion ""
