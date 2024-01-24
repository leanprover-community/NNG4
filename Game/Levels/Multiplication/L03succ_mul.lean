import Game.Levels.Multiplication.L02zero_mul


World "Multiplication"
Level 3
Title "succ_mul"

namespace MyNat

Introduction
"
Similarly we have `mul_succ`
but we're going to need `succ_mul` (guess what it says -- maybe you
are getting the hang of Lean's naming conventions).

The last level from addition world might help you in this level.
If you can't remember what it is, you can go back to the
home screen by clicking the house icon and then taking a look.
You won't lose any progress.
"

TheoremDoc MyNat.succ_mul as "succ_mul" in "*" "
`succ_mul a b` is the proof that `succ a * b = a * b + b`.

It could be deduced from `mul_succ` and `mul_comm`, however this argument
would be circular because the proof of `mul_comm` uses `mul_succ`.
"

/-- For all natural numbers $a$ and $b$, we have
$(\operatorname{succ}\ a) \times b = a\times b + b$. -/
Statement succ_mul
    (a b : ℕ) : succ a * b = a * b + b := by
  induction b with d hd
  · rw [mul_zero]
    rw [mul_zero]
    rw [add_zero]
    rfl
  · rw [mul_succ]
    rw [mul_succ]
    rw [hd]
    rw [add_succ]
    rw [add_succ]
    rw [add_right_comm]
    rfl

TheoremTab "*"
