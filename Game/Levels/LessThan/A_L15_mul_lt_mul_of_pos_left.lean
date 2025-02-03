import Game.Levels.LessThan.A_L14_mul_lt_mul_of_pos_right

World "LessThan"
Level 15
Title "TITLE"

TheoremTab "<"

namespace MyNat

/-- FUNCTION INTRODUCTION -/
TheoremDoc MyNat.mul_lt_mul_of_pos_left as "mul_lt_mul_of_pos_left" in "<"

Introduction "INTRODUCTION"

/-- LEMMA DOCUMENTATION -/
Statement mul_lt_mul_of_pos_left (a b c : ℕ) --level 15
    : b < c → 0 < a → a * b < a * c  := by
  rw [mul_comm a b, mul_comm a c]
  exact mul_lt_mul_of_pos_right a b c



Conclusion "CONCLUSION"
