import Game.Levels.LessThan.A_L05_lt_of_le_of_lt

World "LessThan"
Level 6
Title "< is transitive"

TheoremTab "<"

namespace MyNat

/--
`lt_trans x y z` is a proof that if `x < y` and `y < z` then `x < z`.
More precisely, it is a proof that `x < y → (y < z → x < z)`. In words,
If $x < y$ then (pause) if $y < z$ then $x < z$. -/
TheoremDoc MyNat.lt_trans as "lt_trans" in "<"

Introduction "In this level we show that `<` is transitive.  Try doing
this proof \"with your bare hands\" and also using one of the previous
two levels.  In the latter case, we don't have a proof of the true
proposition that `a<b → a ≤ b`, so showing that or something similar
would be required."

--Question for Kevin, do we want to add le_of_lt?
--This comes for free when show that we have a pre order.
--On the other hand, many other things also come for free,
--In fact, most of this world.

/-- If `a < b` and `b < c`, then `a < c` -/
Statement lt_trans (a b c : ℕ) : a < b → b < c → a < c := by
  intro ⟨n,hnab⟩ ⟨m,hmbc⟩
  use (succ (n + m))
  rw [hmbc,hnab]
  repeat rw [succ_add]
  rw [add_succ,add_assoc]
  rfl

Conclusion "Our tasks now are to develop how `<` interacts with
successor, addition and multiplication.  To that end, our next level
shows that a number is always less than its successor."
