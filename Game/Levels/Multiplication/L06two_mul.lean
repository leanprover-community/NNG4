import Game.Levels.Multiplication.L05one_mul

World "Multiplication"
Level 6
Title "two_mul"

namespace MyNat

Introduction
"
This level is more important than you think; it plays
a useful role when battling a big boss later on.
"

/--
`two_mul m` is the proof that `2 * m = m + m`.
-/
TheoremDoc MyNat.two_mul as "two_mul" in "*"

/-- For any natural number $m$, we have $ 2 \times m = m+m$. -/
Statement two_mul
    (m : ℕ): 2 * m = m + m := by
  rw [two_eq_succ_one, succ_mul, one_mul]
  rfl

TheoremTab "*"

Conclusion "
Here's my solution:
```
rw [two_eq_succ_one, succ_mul, one_mul]
rfl
```
"
