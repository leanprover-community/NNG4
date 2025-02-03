import Game.Levels.LessThan.A_L02_ne_of_lt

World "LessThan"
Level 3
Title "No natural number is less than zero"

TheoremTab "≤"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.not_lt_zero as "not_lt_zero" in "<"

Introduction "In the LessOrEqual world, we showed that zero is LessOrEqual to every
natural number.  In this world, we show that there is not natural number strictly less
than zero."

/-- If $\operatorname{succ}(x) \leq \operatorname{succ}(y)$ then $x \leq y$. -/
Statement not_lt_zero (a : ℕ) : ¬(a < 0)  := by
  intro ⟨n,hn⟩
  rw [succ_add] at hn
  have h1 := succ_ne_zero (a + n)
  exact h1 hn.symm

Conclusion "CONCLUSION"
