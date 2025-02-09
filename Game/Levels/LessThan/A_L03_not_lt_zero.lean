import Game.Levels.LessThan.A_L02_ne_of_lt

World "LessThan"
Level 3
Title "No natural number is less than zero"

TheoremTab "<"

namespace MyNat

/-- `not_lt_zero a` is a proof that if `¬(a < 0)`. In words, for a
natural number `a`, `a` is not less than `0`.
-/
TheoremDoc MyNat.not_lt_zero as "not_lt_zero" in "<"

Introduction "In the `≤` world, we showed that zero is
`≤` to every natural number.  In this world, we show that for
all natural numbers `a`, is not `<` zero."

/--
There is no natural number less than zero.
-/
Statement not_lt_zero (a : ℕ) : ¬(a < 0)  := by
  intro h0
  Hint "You probably want to split up {h0} into its pieces."
  cases h0 with n hn
  Hint "Can you show that {hn} implies that the successor of something is zero?"
  rw [succ_add] at hn
  have h1 := succ_ne_zero (a + n)
  exact h1 hn.symm

Conclusion "Since we have `<` and `≤`, we can combine them to generate
transitivity properties.  In the next three levels we will state and prove
three of them."
