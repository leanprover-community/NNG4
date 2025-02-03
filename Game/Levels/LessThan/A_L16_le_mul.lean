import Game.Levels.LessThan.A_L15_mul_lt_mul_of_pos_left

World "LessThan"
Level 16
Title "TITLE"

TheoremTab "≤"

namespace MyNat

/-- `THEOREM DOC TEXT -/
TheoremDoc MyNat.le_mul as "le_mul" in "≤"

Introduction "INTRODUCTION"

Statement le_mul (a b c d : ℕ ) : a ≤ b → c ≤ d → a * c ≤ b * d := by --level 16
  intro ⟨n,hab⟩ ⟨m,hcd⟩
  rw [hab,hcd,add_mul,mul_add,mul_add]
  use (a * m + (n * c + n * m))
  rw [add_assoc (a * c) ]
  rfl

Conclusion "CONCLUSION"
