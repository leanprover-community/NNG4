import Game.Levels.AdvAddition.L06eq_zero_of_add_right_eq_zero

World "AdvAddition"
Level 7
Title "eq_zero_of_add_left_eq_zero"

LemmaTab "Peano"

namespace MyNat

Introduction
"You can just mimic the previous proof to do this one -- or you can figure out a way
of using it.
"

LemmaDoc MyNat.eq_zero_of_add_eq_zero_left as "eq_zero_of_add_eq_zero_left" in "Add" "
  A proof that $a+b=0 \\implies b=0$.
"

-- **TODO** why `add_eq_zero_right` and not `add_right_eq_zero`?

/-- If $a+b=0$ then $b=0$. -/
Statement eq_zero_of_add_eq_zero_left (a b : ℕ) : a + b = 0 → b = 0 := by
  rw [add_comm]
  exact eq_zero_of_add_eq_zero_right b a

Conclusion "How about this for a proof:

```
rw [add_comm]
exact eq_zero_of_add_eq_zero_right b a
```

You're now ready for LessThanOrEqual World.
"
