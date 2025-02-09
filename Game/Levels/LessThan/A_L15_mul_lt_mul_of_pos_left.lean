import Game.Levels.LessThan.A_L14_mul_lt_mul_of_pos_right

World "LessThan"
Level 15
Title "mul_lt_mul_of_pos_left"

TheoremTab "<"

namespace MyNat



/-- `mul_lt_mul_of_pos_left a b c` is proof that `b < c → 0 < a → a * b < a * c` -/
TheoremDoc MyNat.mul_lt_mul_of_pos_left as "mul_lt_mul_of_pos_left" in "<"

Introduction "In this level we prove that we can pre-multiply both
sides of an inequality by a positive number and retain a valid
inequality.  This statement is closesly related to the previous level
so we won't give hints here.

Question for Kevin.  Do we need this Level?"


/-- 
We can pre-multiply both sides of an inequality by a positive
number and retain a valid inequality.
-/
Statement mul_lt_mul_of_pos_left (a b c : ℕ)
    : b < c → 0 < a → a * b < a * c  := by
  rw [mul_comm a b, mul_comm a c]
  exact mul_lt_mul_of_pos_right a b c



Conclusion "
My Proof:
```
  rw [mul_comm a b, mul_comm a c]
  exact mul_lt_mul_of_pos_right a b c
```
"

