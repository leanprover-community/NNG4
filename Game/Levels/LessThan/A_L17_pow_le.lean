import Game.Levels.LessThan.A_L16_le_mul
import Game.Levels.Power

World "LessThan"
Level 17
Title "Question for Kevin.  I propose we put this in the `≤` world or scrap it.  Actually, we need ≤ and powers, so it can't go in `≤` world."

TheoremTab "^"

namespace MyNat

/-- `pow_le m n a` is a proof that m ≤ n → m ^ a ≤ n ^ a  -/
TheoremDoc MyNat.pow_le as "pow_le" in "<"

Introduction "In this level we show that function that maps a natural
number to (natural number) power of itself if monotone.  This means
that larger or equal numbers are mapped to larger of equal outputs."

Statement pow_le (m n a : ℕ) : m ≤ n → m ^ a ≤ n ^ a := by
  intro hmn
  Hint"Try doing induction on {a}."
  induction a with l hl
  rw [pow_zero,pow_zero]
  exact le_refl 1
  rw [pow_succ]
  rw [pow_succ]
  apply le_mul
  exact hl
  exact hmn

Conclusion "We are now ready to advance to the final boss of this
world: Strong induction.  Click \"Next\" to continue."
