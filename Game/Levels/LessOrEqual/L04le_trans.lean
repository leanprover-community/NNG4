import Game.Levels.LessOrEqual.L03le_succ_self

World "LessOrEqual"
Level 4
Title "x ≤ y and y ≤ z implies x ≤ z"

TheoremTab "≤"

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
TheoremDoc MyNat.le_trans as "le_trans" in "≤"

Introduction "
In this level, we see inequalities as *hypotheses*. We have not seen this before.
The `cases` tactic can be used to take `hxy` apart.
"

/-- If $x \leq y$ and $y \leq z$, then $x \leq z$. -/
Statement le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  Hint "Start with `cases {hxy} with a ha`."
  cases hxy with a ha
  Hint "Now `{ha}` is a proof that `{y} = {x} + {a}`, and `hxy` has vanished. Similarly, you can destruct
  `{hyz}` into its parts with `cases {hyz} with b hb`."
  cases hyz with b hb
  Hint "Now you need to figure out which number to `use`. See if you can take it from here."
  use a + b
  rw [hb, ha]
  exact add_assoc x a b

TheoremTab "≤"

Conclusion "
A passing mathematician remarks that with reflexivity and transitivity out of the way, you have proved that `≤` is a *preorder* on `ℕ`.
"
