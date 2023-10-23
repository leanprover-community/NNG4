import Game.Levels.AdvAddition.L04add_left_eq_self

World "AdvAddition"
Level 5
Title "add_right_eq_self"

LemmaTab "Add"

namespace MyNat

LemmaDoc MyNat.add_right_eq_self as "add_right_eq_self" in "Add" "

`add_right_eq_self x y` is the theorem that $x + y = x\\implies y=0.$
"

Introduction
"`add_right_eq_self x y` is the theorem that $x + y = x\\implies y=0.$
Two ways to do it spring to mind; I'll mention them when you've solved it.
"

/-- $x+y=x\implies y=0$. -/
Statement add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  rw [add_comm]
  exact add_left_eq_self y x

Conclusion "Here's a proof using `add_left_eq_self`:
```
rw [add_comm]
intro h
apply add_left_eq_self at h
exact h
```

and here's an even shorter one using the same idea:
```
rw [add_comm]
exact add_left_eq_self y x
```

Alternatively you can just prove it by induction on `x`
(the dots in the proof just indicate the two goals and
can be omitted):

```
  induction x with d hd
  · intro h
    rw [zero_add] at h
    assumption
  · intro h
    rw [succ_add] at h
    apply succ_inj at h
    apply hd at h
    assumption
```
"
