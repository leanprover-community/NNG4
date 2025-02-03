import Game.Levels.LessThan.A_L12_succ_lt_succ_iff
import Game.Levels.Multiplication

World "LessThan"
Level 13
Title "TITLE"

TheoremTab "<"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.mul_le_mul_of_nonneg_left as "mul_le_mul_of_nonneg_left" in "<"

Introduction "INTRODUCTION"

--drop tactic?

theorem mul_le_mul_of_nonneg_left (a b c: ℕ) --level 13
    : a ≤ b → 0 ≤ c → a * c ≤ b * c := by
  intro ⟨n,hab⟩
  intro cnneg
  clear cnneg
  use (c * n)
  rw [hab,add_mul]
  rw [mul_comm n c]
  rfl

Conclusion "CONCLUSION"
