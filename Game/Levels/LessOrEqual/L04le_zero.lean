import Game.Levels.LessOrEqual.L03le_succ_self

World "LessOrEqual"
Level 4
Title "x ≤ 0 → x = 0"

namespace MyNat

LemmaDoc MyNat.le_zero as "le_zero" in "≤" "
`le_zero x` is a proof of `x ≤ 0 → x = 0`.
"

Introduction "
In this level, our inequality is a *hypothesis*. We have not seen this before.
The `rcases` tactic can be used to take `hx` apart.
"

LemmaDoc MyNat.le_zero as "le_zero" in "≤"
"`le_zero x` is a proof of the implication `x ≤ 0 → x = 0`. "

/-- If $x \leq 0$, then $x=0$. -/
Statement le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  Hint "Start with `cases hx with y hy`. You can get the funny pointy brackets with `\\<` and
  `\\>`, or `\\<>` will give you both at once."
  cases hx with y hy
  Hint "Now `y` is what you have to add to `x` to get `0`, and `hy` is the proof of this."
  Hint (hidden := true) "You want to use `eq_zero_of_add_right_eq_zero`, which you already
  proved, but you'll have to start with `symm at hy`."
  symm at hy
  apply eq_zero_of_add_right_eq_zero at hy
  exact hy

LemmaTab "≤"
