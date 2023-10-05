import Game.Levels.AdvAddition.L10add_left_eq_self

World "AdvAddition"
Level 11
Title "add_right_eq_self"

LemmaTab "Add"

namespace MyNat

LemmaDoc MyNat.add_right_eq_self as "add_right_eq_self" in "Add" "

`add_right_eq_self x y` is the theorem that $x + y = x\\implies y=0.$
"

NewLemma MyNat.add_right_eq_self

Introduction
"`add_right_eq_self x y` is the theorem that $x + y = x\\implies y=0.$
"

/-- $a+n=b+n\implies a=b$. -/
Statement add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  rw [add_comm]
  intro h
  apply add_left_eq_self at h
  assumption

Conclusion "Here's a proof using `add_left_eq_self`:
```
rw [add_comm]
intro h
apply add_left_eq_self at h
assumption
```
"
