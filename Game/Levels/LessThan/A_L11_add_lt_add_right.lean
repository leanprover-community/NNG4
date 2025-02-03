import Game.Levels.LessThan.A_L10_lt_of_add_lt_add_left

World "LessThan"
Level 11
Title "TITLE"

TheoremTab "<"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.add_lt_add_right as "add_lt_add_right" in "<"

Introduction "INTRODUCTION"

/-- TITLE -/
Statement add_lt_add_right (a b : ℕ) : a < b → ∀ c : ℕ, a + c < b + c := by --level 11
  rintro ⟨n,hn⟩
  intro c
  use n
  rw [hn,add_assoc,add_comm n c]
  repeat rw [succ_add]
  rw [add_assoc]
  rfl

Conclusion "We have now shown that the natural numbers form an ordered commutative monoid,
a canonnically ordered commutative monoid, and an ordered cancellable commutative monoid."
