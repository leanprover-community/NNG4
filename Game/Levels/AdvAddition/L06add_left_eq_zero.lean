import Game.Levels.AdvAddition.L05add_right_eq_zero

World "AdvAddition"
Level 6
Title "add_left_eq_zero"

TheoremTab "+"

namespace MyNat

Introduction
"You can just mimic the previous proof to do this one -- or you can figure out a way
of using it.
"

/--  A proof that $a+b=0 \implies b=0$. -/
TheoremDoc MyNat.add_left_eq_zero as "add_left_eq_zero" in "+"

/-- If $a+b=0$ then $b=0$. -/
Statement add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  rw [add_comm]
  exact add_right_eq_zero b a

Conclusion "How about this for a proof:

```
rw [add_comm]
exact add_right_eq_zero b a
```

That's the end of Advanced Addition World! You'll need these theorems
for the next world, `≤` World. Click on \"Leave World\" to access it.
"
