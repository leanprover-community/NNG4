import Game.Levels.LessOrEqual.L05le_zero

World "LessOrEqual"
Level 6
Title "x ≤ y and y ≤ x implies x = y"

namespace MyNat

LemmaDoc MyNat.le_antisymm as "le_antisymm" in "≤" "
`le_antisymm x y` is a proof that if `x ≤ y` and `y ≤ x` then `x = y`.
"

Introduction "
This level asks you to prove *antisymmetry* of $\\leq$.
In other words, if $x \\leq y$ and $y \\leq x$ then $x = y$.
It's the trickiest one so far. Good luck!
"

/-- If $x \leq y$ and $y \leq x$, then $x = y$. -/
Statement le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  cases hxy with a ha
  cases hyx with b hb
  rw [ha]
  rw [ha, add_assoc] at hb
  symm at hb
  apply add_right_eq_self at hb
  apply eq_zero_of_add_right_eq_zero at hb
  rw [hb, add_zero]
  rfl

LemmaTab "≤"

Conclusion "
Here's my proof:
```
cases hxy with a ha
cases hyx with b hb
rw [ha]
rw [ha, add_assoc] at hb
symm at hb
apply add_right_eq_self at hb
apply eq_zero_of_add_right_eq_zero at hb
rw [hb, add_zero]
rfl
```

A passing mathematician remarks that with antisymmetry as well,
you have proved that `≤` is a *partial order* on `ℕ`.

The next level, the boss level of this world, is to prove
that `≤` is a total order.
"
