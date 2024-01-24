import Game.Levels.LessOrEqual.L02zero_le

World "LessOrEqual"
Level 3
Title "x ≤ succ x"

namespace MyNat

/-- `le_succ_self x` is a proof that `x ≤ succ x`. -/
TheoremDoc MyNat.le_succ_self as "le_succ_self" in "≤"

Introduction "If you `use` the wrong number, you get stuck with a goal you can't prove.
What number will you `use` here?"

/-- If $x$ is a number, then $x \le \operatorname{succ}(x)$. -/
Statement le_succ_self (x : ℕ) : x ≤ succ x := by
  use 1
  rw [succ_eq_add_one]
  rfl

TheoremTab "+"

Conclusion "
Here's a two-liner:
```
use 1
exact succ_eq_add_one x
```

This works because `succ_eq_add_one x` is a proof of `succ x = x + 1`.
"

/-
Introduction
"
Because constantly rewriting `zero_add` and `add_zero` is a bit dull,
let's unlock the `ring` tactic. This will prove any goal which is \"true
in the language of ring theory\", for example `a + b + c = c + b + a`.
It doesn't understand `succ` though, so use `succ_eq_add_one` in this
level to get rid of it.
"
-/
