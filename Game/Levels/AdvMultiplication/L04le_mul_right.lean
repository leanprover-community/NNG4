import Game.Levels.AdvMultiplication.L03one_le_of_zero_ne

World "AdvMultiplication"
Level 4
Title "le_mul_right"

LemmaTab "≤"

namespace MyNat

LemmaDoc MyNat.le_mul_right as "le_mul_right" in "≤" "
`le_mul_right a b` is a proof that `a * b ≠ 0 → a ≤ a * b`.

It's one way of saying that a divisor of a positive number
has to be at most that number.
"

Introduction
"
In Prime Number World we will be proving that $2$ is prime.
To do this, we will have to rule out things like $2 \neq 323846224*3453453459182.$
We will do this by proving that any factor of $2$ is at most $2$,
which we will do using this lemma. The proof I have in mind uses
everything which we've proved in this world so far.
"

Statement le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  apply mul_left_ne_zero at h
  apply one_le_of_zero_ne at h
  apply mul_le_mul_right 1 b a at h
  rw [one_mul, mul_comm] at h
  exact h

Conclusion "Here's what I was thinking of:
```
apply mul_left_ne_zero at h
apply one_le_of_zero_ne at h
apply mul_le_mul_right 1 b a at h
rw [one_mul, mul_comm] at h
exact h
```
"
