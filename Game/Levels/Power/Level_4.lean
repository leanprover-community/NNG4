import Game.Levels.Power.Level_3



World "Power"
Level 4
Title "one_pow"

open MyNat

/-- For all naturals $m$, $1 ^ m = 1$. -/
Statement MyNat.one_pow
    (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with t ht
  · rw [pow_zero]
    rfl
  · rw [pow_succ]
    rw [ht]
    rw [mul_one]
    rfl

LemmaTab "Pow"
