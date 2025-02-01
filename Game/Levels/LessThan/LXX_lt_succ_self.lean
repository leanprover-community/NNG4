import Game.Levels.LessThan.L04_lt_iff_succ_le

World "LessThan"
Level 5
Title "x < succ x"

namespace MyNat

/-- `le_succ_self x` is a proof that `x ≤ succ x`. -/
TheoremDoc MyNat.lt_succ_self as "lt_succ_self" in "<"

Introduction "If you `use` the wrong number, you get stuck with a goal you can't prove.
What number will you `use` here?"

/-- If $x$ is a number, then $x \le \operatorname{succ}(x)$. -/
Statement lt_succ_self (x : ℕ) : x < succ x := by
  constructor
  use 1
  rw [succ_eq_add_one]
  rfl
  intro h1
  induction x with k hk
  have h2 := zero_ne_succ 0
  exact h2 h1
  exact hk (succ_inj k (succ k) h1)


TheoremTab "<"

Conclusion ""

