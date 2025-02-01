import Game.Levels.LessThan.L05_succ_lt_succ

World "LessThan"
Level 6
Title "x < y and y ≤ z implies x < z"

TheoremTab "<"

namespace MyNat


TheoremDoc MyNat.lt_of_le_of_lt as "lt_of_le_of_lt" in "<"

Introduction ""

/-- If $x \lt y$ and $y \leq z$, then $x \lt z$. -/
Statement lt_of_le_of_lt (x y z : ℕ) (hxy : x < y) (hyz : y ≤ z) : x < z := by
  cases hxy with a ha
  cases hyz with b hb
  use (a + b)
  rw [hb,ha,add_succ,succ_add,add_succ,add_assoc]
  rfl
TheoremTab "<"

Conclusion ""


