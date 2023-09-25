import Game.Levels.Multiplication.L06two_mul

World "Multiplication"
Level 7
Title "mul_add"

namespace MyNat

Introduction
"
Our next goal is \"left and right distributivity\",
meaning $a(b+c)=ab+ac$ and $(b+c)a=ba+ca$. Rather than
these slightly pompous names, the name of the proof
of `a * (b + c) = a * b + a * c` in Lean is `mul_add`.
Note that the left hand side contains a multiplication
and then an addition.
"

LemmaDoc MyNat.mul_add as "mul_add" in "Mul" "Multiplication distributes
over addition on the left.

`mul_add a b c` is the proof that `a * (b + c) = a * b + a * c`."

/-- Multiplication is distributive over addition on the left.
In other words, for all natural numbers $a$, $b$ and $t$, we have
$a(b + c) = ab + ac$. -/
Statement mul_add
    (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  Hint "You can do induction on any of the three variables. Some choices
  are harder to push through than others."
  Hint (hidden := true) "Induction on `a` is the most troublesome, then `b`,
  and `c` is the easiest."
  induction c with d hd
  rw [add_zero, mul_zero, add_zero]
  rfl
  rw [add_succ, mul_succ, hd, mul_succ, add_assoc]
  rfl

LemmaTab "Mul"
