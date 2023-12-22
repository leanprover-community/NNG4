import Game.Levels.LessOrEqual.L08le_total

World "LessOrEqual"
Level 9
Title "succ x ≤ succ y → x ≤ y"

LemmaTab "≤"

namespace MyNat

LemmaDoc MyNat.succ_le_succ as "succ_le_succ" in "≤" "
`succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`.
"

Introduction "
We've proved that `x ≤ 0` implies `x = 0`. The last two levels
in this world will prove which numbers are `≤ 1` and `≤ 2`.
This lemma will be helpful for them.
"

/-- If $\operatorname{succ}(x) \leq \operatorname{succ}(y)$ then $x \leq y$. -/
Statement succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  cases hx with d hd
  use d
  rw [succ_add] at hd
  apply succ_inj at hd
  exact hd

Conclusion "
Here's my proof:
```
cases hx with d hd
use d
rw [succ_add] at hd
apply succ_inj at hd
exact hd
```
"
