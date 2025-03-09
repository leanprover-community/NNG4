import Game.Levels.LessThan.B_L03_lt_succ_self

World "LessThan"
Level 4
Title "not_lt_zero"

namespace MyNat

/-- `not_lt_zero a`is a proof that `¬(a < 0)`.-/
TheoremDoc MyNat.not_lt_zero as "not_lt_zero" in "<"

Introduction "In this level, we show that there is no natural number less than zero."

/--If `a` is a natural number the ¬(a < 0). -/
Statement not_lt_zero (a : ℕ) : ¬(a < 0) := by
  intro h0
  cases h0 with θ h0
  Hint "One of main tools is the fact that zero is not the successor of a natural number, try to use that here."
  rw [succ_add] at h0
  have h1 := zero_ne_succ (a + θ)
  exact h1 h0

Conclusion "CONCLUSION"








Conclusion "CONCLUSION."






