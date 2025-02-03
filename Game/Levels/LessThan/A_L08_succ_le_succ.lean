import Game.Levels.LessThan.A_L07_lt_succ_self

World "LessThan"
Level 8
Title "succ x ≤ succ y ↔ x ≤ y"

TheoremTab "≤" --question for kevin in this tab or in < tab?

namespace MyNat

/-- `succ_le_succ_iff x y` is a proof that if `succ x ≤ succ y` iff `x ≤ y`. -/
TheoremDoc MyNat.succ_le_succ_iff as "succ_le_succ_iff" in "≤"

Introduction "To show that the natural numbers for a (A CERTAIN
ALGEBRAIC STRUCTURE), we need to add a result relating to the the `≤`
operator, we add them here"

/-- If $\operatorname{succ}(x) \leq \operatorname{succ}(y)$ iff $x \leq y$. -/
Statement succ_le_succ_iff (x y: ℕ) : succ x ≤ succ y ↔ x ≤ y := by
  constructor
  exact (succ_le_succ x y)
  intro ⟨a,ha⟩
  rw [ha]
  use a
  rw [succ_add]
  rfl


Conclusion "CONCLUSION"
