import Game.Levels.AdvAddition.L06add_right_eq_zero

World "AdvAddition"
Level 7
Title "add_left_eq_zero"

LemmaTab "+"

namespace MyNat

Introduction
"You can just mimic the previous proof to do this one -- or you can figure out a way
of using it.
"

LemmaDoc MyNat.add_left_eq_zero as "add_left_eq_zero" in "+" "
  A proof that $a+b=0 \\implies b=0$.
"

/-- If $a+b=0$ then $b=0$. -/
Statement add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  rw [add_comm]
  exact add_right_eq_zero b a

Conclusion "How about this for a proof:

```
rw [add_comm]
exact add_right_eq_zero b a
```

We've now proved all the theorems you'll need for `≤` World.
"
