import Game.Levels.LessThan.B_L04_not_lt_zero

World "LessThan"
Level 5
Title "lt_iff_le_not_le"

namespace MyNat

/-- `lt_iff_le_not_le a b` is a proof that  `a < b ↔ (a ≤ b) ∧ ¬(b ≤ a)`. -/
TheoremDoc MyNat.lt_iff_le_not_le as "lt_iff_le_not_le" in "<"

Introduction "In this level, "

/--If `a` and `b` are natural numbers, then `a < b` iff `a ≤ b` and `¬(b ≤ a)`. -/
Statement lt_iff_le_not_le (a b : ℕ) :
  a < b ↔ (a ≤ b) ∧ ¬(b ≤ a) := by
  constructor
  rintro ⟨r,h0⟩
  constructor
  use (succ r)
  rw [add_succ,←succ_add]
  exact h0
  rintro ⟨r1,h1⟩
  rw [h0] at h1
  rw [add_assoc] at h1
  rw [succ_add,←add_succ] at h1
  have h2 := add_right_eq_self a (succ (r + r1)) h1.symm
  have h3 := succ_ne_zero (r + r1)
  exact h3 h2
  rintro ⟨⟨r,h0⟩,h1⟩
  rw [h0]
  cases r with l
  exfalso
  rw [add_zero] at h0
  apply h1
  use 0
  rw [add_zero,h0]
  rfl
  use l
  rw [add_succ,succ_add]
  rfl

Conclusion "CONCLUSION."






