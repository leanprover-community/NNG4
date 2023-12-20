import Game.Levels.LessOrEqual.L08le_total

World "LessOrEqual"
Level 9
Title "succ x ≤ succ y → x ≤ y"

LemmaTab "≤"

namespace MyNat

LemmaDoc MyNat.le_of_succ_le_succ as "le_of_succ_le_succ" in "≤" "
`le_of_succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`.
"

Introduction "
The last goal in this world is to prove which numbers are `≤ 2`.
This lemma will be helpful for that.
"

/-- If $\operatorname{succ}(x) \leq \operatorname{succ}(y)$ then $x \leq y$. -/
Statement le_of_succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
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

This lemma can be helpful for the next two levels.
"
