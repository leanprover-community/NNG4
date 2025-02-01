import Game.Levels.LessThan.L07_add_lt_iff_right

World "LessThan"
Level 8
Title "x < y and y < z implies x < z"

TheoremTab "<"

namespace MyNat

/--
`lt_trans x y z` is a proof that if `x < y` and `y < z` then `x < z`.
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
  rcases hxy with ⟨hxy0,hxy1⟩
  rcases hyz with ⟨hyz0,hyz1⟩
  constructor
  exact le_trans x y z hxy0 hyz0
  intro h0
  rw [h0] at hxy0
  exact hyz1 (le_antisymm y z hyz0 hxy0)


TheoremTab "<"

Conclusion ""


