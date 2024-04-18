import Game.Levels.AdvAddition.L03add_left_eq_self

World "AdvAddition"
Level 4
Title "add_right_eq_self"

TheoremTab "+"

namespace MyNat

/-- `add_right_eq_self x y` is the theorem that $x + y = x \implies y=0.$ -/
TheoremDoc MyNat.add_right_eq_self as "add_right_eq_self" in "+"

Introduction
"`add_right_eq_self x y` is the theorem that $x + y = x\\implies y=0.$
Two ways to do it spring to mind; I'll mention them when you've solved it.
"

/-- $x+y=x\implies y=0$. -/
Statement add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  Branch
    intro h
    rw [add_comm] at h
    rw [add_left_eq_self x y] at h
    · rw [add_zero] at h
      exact h
    Hint "This state is not provable! Did you maybe use `rw [add_left_eq_self] at h`
    instead of `apply [add_left_eq_self] at h`? You can complare the two in the inventory."
    -- not ideal to have the hint duplicated, but it's not obvious if they'd use `add_comm`
    -- or not
    rw [add_comm] at h
    Hint "This state is not provable! Did you maybe use `rw [add_left_eq_self] at h`
    instead of `apply [add_left_eq_self] at h`? You can complare the two in the inventory."
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
