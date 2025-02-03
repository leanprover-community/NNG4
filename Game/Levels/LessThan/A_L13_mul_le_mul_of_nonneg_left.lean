import Game.Levels.LessThan.A_L12_succ_lt_succ_iff
import Game.Levels.Multiplication

World "LessThan"
Level 13
Title "TITLE"

TheoremTab "<"

namespace MyNat

/-- `mul_le_mul_of_nonneg_left a b c` is a proof that if `a ≤ b` then a * c ≤ b * c -/
TheoremDoc MyNat.mul_le_mul_of_nonneg_left as "mul_le_mul_of_nonneg_left" in "<"

Introduction "INTRODUCTION"

--note to Kevin, I removed the requirement that `0 ≤ c`, since that always 
--happends, If some of the instances need this, then I suppose we could use
--this theorem as a base and use `zero_le c`.


Statement mul_le_mul_of_nonneg_left (a b c: ℕ) --level 13
    : a ≤ b → a * c ≤ b * c := by
  intro ⟨n,hab⟩
  use (c * n)
  rw [hab,add_mul]
  rw [mul_comm n c]
  rfl

Conclusion "CONCLUSION"
