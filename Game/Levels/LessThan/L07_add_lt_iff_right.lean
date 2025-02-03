import Game.Levels.LessThan.L0

World "LessThan"
Level 9
Title "succ x ≤ succ y → x ≤ y"

TheoremTab "≤"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.succ_le_succ as "succ_le_succ" in "<"

Introduction ""

/-- If $\operatorname{succ}(x) \leq \operatorname{succ}(y)$ then $x \leq y$. -/
Statement succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  cases hx with d hd
  use d
  rw [succ_add] at hd
  apply succ_inj at hd
  exact hd

Conclusion ""
