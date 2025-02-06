import Game.Levels.LessThan.A_L10_lt_of_add_lt_add_left

World "LessThan"
Level 11
Title "add_lt_add_right"

TheoremTab "<"

namespace MyNat

/-- `add_lt_add_right a b` is a proof that `a < b → ∀ c : ℕ, a + c < b + c`.
-/
TheoremDoc MyNat.add_lt_add_right as "add_lt_add_right" in "<"

Introduction "In this level we show that we can add any number to both sides of an inequality and retain a inequality."

Statement add_lt_add_right (a b : ℕ)
  : a < b → ∀ c : ℕ, a + c < b + c := by
    intro ⟨n,hn⟩
    intro c
    Hint "What number is morally `b - succ a`?"
    use n
    Hint "You can take it from here."
    rw[hn,add_assoc,add_comm n c]
    repeat rw [succ_add]
    rw [add_assoc]
    rfl

Conclusion "We have now shown that the natural numbers form an ordered
commutative monoid, a canonnically ordered commutative monoid, and an
ordered cancellable commutative monoid."
