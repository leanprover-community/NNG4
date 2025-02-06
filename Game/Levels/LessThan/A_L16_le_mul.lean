import Game.Levels.LessThan.A_L15_mul_lt_mul_of_pos_left

World "LessThan"
Level 16
Title "mul_lt_mul_of_pos_left"

TheoremTab "<"  --double check that this is correct.

namespace MyNat

/-- `le_mul a b c d` is a proof that `a ≤ b → c ≤ d → a * c ≤ b * d` -/
TheoremDoc MyNat.le_mul as "le_mul" in "≤" --double check that this is correct

Introduction "In this level we show that we can multiply two `≤`-relations term-by-term and retain
a valid `≤`-relation."

Statement le_mul (a b c d : ℕ ) : a ≤ b → c ≤ d → a * c ≤ b * d := by
  Hint"What number is `b * d - a * c`?"
  intro ⟨n,hab⟩ ⟨m,hcd⟩
  rw [hab,hcd,add_mul,mul_add,mul_add]
  use (a * m + (n * c + n * m))
  rw [add_assoc (a * c) ]
  rfl




