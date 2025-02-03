import Game.Levels.LessThan.A_L11_add_lt_add_right


World "LessThan"
Level 12
Title "TITLE"

TheoremTab "<"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.succ_lt_succ_iff as "succ_lt_succ_iff" in "<"

Introduction "INTRODUCTION"

Statement succ_lt_succ_iff (a b : ℕ) : succ a < succ b ↔ a < b := by --level 12
  rw [lt_iff_succ_le,lt_iff_succ_le]
  exact succ_le_succ_iff (succ a) b

Conclusion "CONCLUSION"
