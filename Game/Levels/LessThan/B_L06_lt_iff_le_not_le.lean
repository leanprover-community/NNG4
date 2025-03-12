import Game.Levels.LessThan.B_L05_not_lt_zero

World "LessThan"
Level 6
Title "lt_iff_le_not_le"

namespace MyNat

/-- `lt_iff_le_not_le a b` is a proof that  `a < b ↔ (a ≤ b) ∧ ¬(b ≤ a)`. -/
TheoremDoc MyNat.lt_iff_le_not_le as "lt_iff_le_not_le" in "<"

Introduction "There are many equivalent ways we could have defined the
`<` relation.  The one that we chose allows the proofs in this world
to be simpler, but isn't the default way that Lean would have defined
it.  In this level, we show that our definition is equivalent to
Lean's default definition of `<`."

/--If `a` and `b` are natural numbers, then `a < b` iff `a ≤ b` and `¬(b ≤ a)`. -/
Statement lt_iff_le_not_le (a b : ℕ) :
  a < b ↔ (a ≤ b) ∧ ¬(b ≤ a) := by
  constructor
  intro h0
  cases h0 with r h0
  constructor
  use (succ r)
  rw [add_succ,←succ_add]
  exact h0
  intro h1
  cases h1 with r1 h1  
  rw [h0] at h1
  rw [add_assoc] at h1
  rw [succ_add,←add_succ] at h1
  have h2 := add_right_eq_self a (succ (r + r1)) h1.symm
  have h3 := succ_ne_zero (r + r1)
  exact h3 h2
  intro h0
  cases h0 with h0 h1
  cases h0 with r h0
  rw [h0]
  cases r with l
  rw [add_zero]  
  exfalso
  rw [add_zero] at h0
  apply h1
  use 0
  rw [add_zero,h0]
  rfl
  use l
  rw [add_succ,succ_add]
  rfl

Conclusion "The mathematician who passed by after level XXX, remarks
that you have shown that the natural numbers and our choice for the
definition of `<`, form a preorder, a partial order and a linear
order.  Question for Kevin: Do we want to mention why this is important as far as getting new theorems 'for free'?"

instance : Preorder ℕ := {
  le_refl := le_refl
  le_trans := le_trans
  lt_iff_le_not_le := lt_iff_le_not_le
}

instance : PartialOrder ℕ := {
  le_antisymm := le_antisymm
}

instance : LinearOrder ℕ :=
{
  le_total := le_total
  decidableLE := instDecLE
}
