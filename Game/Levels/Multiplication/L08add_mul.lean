import Game.Levels.Multiplication.L07mul_add

World "Multiplication"
Level 8
Title "add_mul"

namespace MyNat

Introduction
"
`add_mul` is just as fiddly to prove by induction; the proof using
`add_comm` is easier.

Don't forget that `add_comm` just changes the first `x + y` which it
sees to `y + x`. If you want to be more targetted, `add_comm b c`
only changes `b + c` to `c + b`.
"

LemmaDoc MyNat.add_mul as "add_mul" in "Mul" "
`add_mul a b c` is a proof that $(a+b)c=ac+bc$.
"
/-- Addition is distributive over multiplication.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$(a + b) \times c = ac + bc$. -/
Statement add_mul
    (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  induction b with d hd
  · rw [zero_mul]
    rw [add_zero]
    rw [add_zero]
    rfl
  · rw [add_succ]
    rw [succ_mul]
    rw [hd]
    rw [succ_mul]
    rw [add_assoc]
    rfl

LemmaTab "Mul"
