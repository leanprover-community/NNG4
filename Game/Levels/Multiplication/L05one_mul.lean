import Game.Levels.Multiplication.L04mul_comm

World "Multiplication"
Level 5
Title "one_mul"

namespace MyNat

Introduction
"
You can prove this one in at least three ways.
Either by induction, or by using `succ_mul`, or
by using commutativity. Which do you think is quickest?
"

LemmaDoc MyNat.one_mul as "one_mul" in "Mul" "
  `one_mul m` is the proof `1 * m = m`.
"

/-- For any natural number $m$, we have $ 1 \times m = m$. -/
Statement one_mul
    (m : ℕ): 1 * m = m := by
  rw [mul_comm, mul_one]
  rfl

LemmaTab "Mul"
