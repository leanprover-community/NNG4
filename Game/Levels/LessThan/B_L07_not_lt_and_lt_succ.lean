import Game.Levels.LessThan.B_L06_lt_succ_iff_le

World "LessThan"
Level 7
Title "not_lt_and_lt_succ"

namespace MyNat

/-- `not_lt_and_lt_succ m n` is a proof that no number is both stricly
greater than another number and strictly less than the other
number's successor.-/
TheoremDoc MyNat.not_lt_and_lt_succ as "not_lt_and_lt_succ" in "<"

Introduction "You don't need this level to fight the final boss, but
it is good training.  This level shows that there is no natural number
that is both greater than a number `n` and less than `n + 1`.  This is
not true for the rational numbers nor the real numbers.  It is true
for integers, though."

/--If `m` and `n` are natural numbers, then `¬( (n < m) ∧ (m < succ n))`. -/
Statement not_lt_and_lt_succ (m n : ℕ) : ¬( (n < m) ∧ (m < succ n )) := by
  rintro ⟨h0,h1⟩
  rw [lt_succ_iff_le] at h1
  rw [lt_iff_le_not_le] at h0
  rcases h0 with ⟨_h1,h01⟩
  exact h01 h1

Conclusion "You are now ready to fight the final boss."
