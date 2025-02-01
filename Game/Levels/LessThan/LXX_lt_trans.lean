import Game.Levels.LessThan.L03_lt_succ_self

World "LessThan"
Level 4
Title "x < y and y < z implies x < z"

TheoremTab "<"

namespace MyNat

/--
`le_trans x y z` is a proof that if `x ≤ y` and `y ≤ z` then `x ≤ z`.
More precisely, it is a proof that `x ≤ y → (y ≤ z → x ≤ z)`. In words,
If $x \le y$ then (pause) if $y \le z$ then $x \le z$.

## A note on associativity

In Lean, `a + b + c` means `(a + b) + c`, because `+` is left associative. However
`→` is right associative. This means that `x ≤ y → y ≤ z → x ≤ z` in Lean means
exactly that `≤` is transitive. This is different to how mathematicians use
$P \implies Q \implies R$; for them, this usually means that $P \implies Q$
and $Q \implies R$.
-/
TheoremDoc MyNat.lt_trans as "lt_trans" in "<"

Introduction ""

/-- If $x \leq y$ and $y \leq z$, then $x \leq z$. -/
Statement lt_trans (x y z : ℕ) (hxy : x < y) (hyz : y < z) : x < z := by
  cases hxy with a ha
  cases hyz with b hb
  use (a + b).succ
  rw [ha] at hb
  rw [add_succ,add_assoc,add_comm (succ a) b,add_succ,add_succ,add_comm b a] at hb
  rw [hb]
  rw [add_succ,add_succ]
  rfl

TheoremTab "<"

Conclusion ""


