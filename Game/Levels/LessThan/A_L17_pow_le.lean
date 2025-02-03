import Game.Levels.LessThan.A_L16_le_mul
import Game.Levels.Power

World "LessThan"
Level 17
Title "TITLE"

TheoremTab "^"

namespace MyNat

/-- `pow_le m n a` is a proof that m ≤ n → m ^ a ≤ n ^ a  -/
TheoremDoc MyNat.pow_le as "pow_le" in "<"

Introduction "INTRODUCTION"

Statement pow_le (m n a : ℕ) : m ≤ n → m ^ a ≤ n ^ a := by --level 17
  intro hmn
  induction a with l hl
  rw [pow_zero,pow_zero]
  exact le_refl 1
  --repeat rw [pos_succ]  not sure why this doesn't do anything.
  rw [pow_succ]
  rw [pow_succ]
  apply le_mul
  exact hl
  exact hmn

Conclusion "CONCLUSION"
