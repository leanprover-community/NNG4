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

"
/-- If $x \leq 0$, then $x=0$. -/
Statement le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  cases hx with y hy
  symm at hy
  apply eq_zero_of_add_right_eq_zero at hy
  exact hy

LemmaTab "≤"

/-
Introduction
"
Because constanly rewriting `zero_add` and `add_zero` is a bit dull,
let's unlock the `ring` tactic. This will prove any goal which is \"true
in the language of ring theory\", for example `a + b + c = c + b + a`.
It doesn't understand `succ` though, so use `succ_eq_add_one` in this
level to get rid of it.
"
-/
