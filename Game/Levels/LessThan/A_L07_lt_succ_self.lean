import Game.Levels.LessThan.A_L06_lt_trans

World "LessThan"
Level 7
Title "A number is (strictly) less than is own successor"

TheoremTab "<"

namespace MyNat

/-- `lt_succ_self a` is a proof that a natural number is less than its successor. -/
TheoremDoc MyNat.lt_succ_self as "lt_succ_self" in "<"

Introduction ""

/-- a < succ a -/
Statement lt_succ_self (a : ℕ) : a < succ a := by
  use 0
  have h1 := add_zero (succ a)
  exact h1.symm

Conclusion "Conclusion"
