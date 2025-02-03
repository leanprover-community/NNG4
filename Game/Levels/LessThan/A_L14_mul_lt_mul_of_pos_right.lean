import Game.Levels.LessThan.A_L13_mul_le_mul_of_nonneg_left

World "LessThan"
Level 14
Title "TITLE"

TheoremTab "<"

namespace MyNat

/-- `mul_lt_mul_of_pos_right a b c ` is a proof that `b < c → 0 < a → b * a < c * a`. -/
TheoremDoc MyNat.mul_lt_mul_of_pos_right as "mul_lt_mul_of_pos_right" in "<"

Introduction "INTRODUCTION"

Statement mul_lt_mul_of_pos_right (a b c : ℕ) --level 14
    : b < c → 0 < a → b * a < c * a := by
  intro ⟨n,hbc⟩
  intro ⟨d,ha⟩
  rw [succ_add,zero_add] at ha
  rw [hbc,ha]
  rw [add_mul,succ_mul]
  use (d + n * succ d)
  rw [mul_succ,mul_succ,add_succ,succ_add,succ_add]
  rw [add_assoc ((b * d) + b)]
  rfl

Conclusion "We have shown that the natural numbers are an ordered semiring."
