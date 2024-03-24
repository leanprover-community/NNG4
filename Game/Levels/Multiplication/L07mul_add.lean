import Game.Levels.Multiplication.L06two_mul

World "Multiplication"
Level 7
Title "mul_add"

namespace MyNat

Introduction
"
Our next goal is \"left and right distributivity\",
meaning $a(b+c)=ab+ac$ and $(b+c)a=ba+ca$. Rather than
these slightly pompous names, the name of the proofs
in Lean are descriptive. Let's start with
`mul_add a b c`, the proof of `a * (b + c) = a * b + a * c`.
Note that the left hand side contains a multiplication
and then an addition.
"

/--
Multiplication distributes
over addition on the left.

`mul_add a b c` is the proof that `a * (b + c) = a * b + a * c`.
-/
TheoremDoc MyNat.mul_add as "mul_add" in "*"

/-- Multiplication is distributive over addition on the left.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$a(b + c) = ab + ac$. -/
Statement mul_add
    (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  Hint "You can do induction on any of the three variables. Some choices
  are harder to push through than others. Can you do the inductive step in
  5 rewrites only?"
  Hint (hidden := true) "Induction on `a` is the most troublesome, then `b`,
  and `c` is the easiest."
  induction c with d hd
  rw [add_zero, mul_zero, add_zero]
  rfl
  rw [add_succ, mul_succ, hd, mul_succ, add_assoc]
  rfl

TheoremTab "*"

Conclusion "
Here's my solution:
```
induction c with d hd
rw [add_zero, mul_zero, add_zero]
rfl
rw [add_succ, mul_succ, hd, mul_succ, add_assoc]
rfl
```

Inducting on `a` or `b` also works, but takes longer.
"
