import Game.Levels.LessThan.L04_le_iff_lt_or_eq

World "LessThan"
Level 5
Title "not_lt_zero"

namespace MyNat

/-- `not_lt_zero a`is a proof that `¬(a < 0)`.-/
TheoremDoc MyNat.not_lt_zero as "not_lt_zero" in "<"

Introduction "In this level, we show that there is no natural number less than zero."

/--If `a` is a natural number the ¬(a < 0). -/
Statement not_lt_zero (a : ℕ) : ¬(a < 0) := by
  intro h0
  Hint "Use `cases` to split up `{h0}`."
  cases h0 with θ h0
  Hint "One of main tools is the fact that zero is not the successor
  of a natural number, (`zero_ne_succ` or `succ_ne_zero`). Try to use
  one of those here."
  rw [succ_add] at h0
  have h1 := zero_ne_succ (a + θ)
  exact h1 h0

Conclusion "Nice job.  In the next level you will show that our
definition of `<`, is equivalent to Lean's default way of defining it.
Click \"Next\" to continue."










