import Game.Levels.LessThan.B_L03_lt_succ_self


World "LessThan"
Level 4
Title "le_iff_lt_or_eq"

namespace MyNat

/-- `le_iff_lt_or_eq a b `is a proof that `a ≤ b` iff `a < b' or a = b'. -/
TheoremDoc MyNat.le_iff_lt_or_eq as "le_iff_lt_or_eq" in "<"

Introduction "This level shows that `a ≤ b ↔ (a < b) ∨ (a = b)`.  In
spoken form (\"`a` is less than or equal to `b` iff `a` is less than or
equal to `b`\"); this is a tautology, so it is a worthwhile exercise to
check that our mathematical definitions also make linguistic sense."

/--If `a` and `b` are  natural numbers, then `a ≤ b` iff (`a < b` or `a = b`).
-/
Statement le_iff_lt_or_eq (a b : ℕ) : a ≤ b ↔ a < b ∨ a = b := by
  constructor
  intro h0
  cases h0 with l h0
  cases l with m
  right
  rw [h0,add_zero]
  rfl
  left
  rw [h0]
  use m
  rw [add_succ,succ_add]
  rfl
  intro h0
  cases h0 with h0 h0
  cases h0 with l h0
  use succ l
  rw [h0,add_succ,succ_add]
  rfl
  rw [h0]
  apply le_refl


Conclusion "Nice job. In the `≤`-world you showed that for all natural
numbers a, we have `0 ≤ a`. In the next level, you will show that zero
is not greater than any natural number."






