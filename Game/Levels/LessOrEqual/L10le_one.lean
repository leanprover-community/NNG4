import Game.Levels.LessOrEqual.L09succ_le_succ
World "LessOrEqual"
Level 10
Title "x ≤ 1"

TheoremTab "≤"

namespace MyNat

/-- `le_one x` is a proof that if `x ≤ 1` then `x = 0` or `x = 1`. -/
TheoremDoc MyNat.le_one as "le_one" in "≤"

Introduction "
We've seen `le_zero`, the proof that if `x ≤ 0` then `x = 0`.
Now we'll prove that if `x ≤ 1` then `x = 0` or `x = 1`.
"

/-- If $x \leq 1$ then either $x = 0$ or $x = 1$. -/
Statement le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with y
  left
  rfl
  rw [one_eq_succ_zero] at hx ⊢
  apply succ_le_succ at hx
  apply le_zero at hx
  rw [hx]
  right
  rfl

Conclusion "
Here's my proof:
```
cases x with y
left
rfl
rw [one_eq_succ_zero] at hx ⊢
apply succ_le_succ at hx
apply le_zero at hx
rw [hx]
right
rfl
```

If you solved this level then you should be fine with the next level!
"
