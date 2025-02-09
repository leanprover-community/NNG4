import Game.Levels.LessThan.A_L03_not_lt_zero

World "LessThan"
Level 4
Title "lt_of_lt_of_le"

TheoremTab "<"

namespace MyNat

/--
`lt_of_lt_of_le x y z` is a proof that if `x < y` and `y ≤ z` then `x < z`.
More precisely, it is a proof that `x < y → (y ≤ z → x < z)`. In words,
If $x < y$ then (pause) if $y \le z$ then $x < z$.-/
TheoremDoc MyNat.lt_of_lt_of_le as "lt_of_lt_of_le" in "<"

Introduction"Before we prove that `<` is transitive, we show a
stronger result:  It suffices to have proofs for both `x < y` and `y ≤
z` to generate a proof of `x < z`.  That is your task in this level.
Remember, your goal in this level is to generate/discover a number `n`
that is morally `c - succ a`."

/-- If `a < b` and `b ≤ c` then `a < c` -/
Statement lt_of_lt_of_le (a b c: ℕ) : a < b → b ≤ c → a < c := by
  intro hab
  Hint"You probably want to split {hab}."
  cases hab with n hab
  intro hbc
  Hint"You probably want to split {hbc}."
  cases hbc with m hbc
  Hint  "You can take it from here.  If subtraction was defined, what number
  would `{c} - succ {a}` be?"
  use (n + m)
  rw [hbc,hab,add_assoc]
  rfl

Conclusion "The next level is closely related."
