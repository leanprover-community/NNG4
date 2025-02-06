import Game.Levels.LessThan.A_L06_lt_trans

World "LessThan"
Level 7
Title "A number is less than is own successor"

TheoremTab "<"

namespace MyNat

/-- `lt_succ_self a` is a proof that `a < succ a`. In words, a natural
number `a`, is less than it's own successor.-/
TheoremDoc MyNat.lt_succ_self as "lt_succ_self" in "<"

Introduction "In the `≤` world, we had proved that a natural number is
is less or equal to its successor.  Now we strengthen this result to
show that it is less than its successor."

Statement lt_succ_self (a : ℕ) : a < succ a := by
  Hint"If subtractions was defined, what number would `(succ a) - (succ a)` be?"
  use 0
  have h1 := add_zero (succ a)
  exact h1.symm

Conclusion
"My proof:
```
use 0
have h1 := add_zero (succ a)
exact h1.symm
```
"
