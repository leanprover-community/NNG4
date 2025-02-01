import Game.Levels.AdvMultiplication.L04one_le_of_ne_zero

World "AdvMultiplication"
Level 5
Title "le_mul_right"

TheoremTab "≤"

namespace MyNat

/--
`le_mul_right a b` is a proof that `a * b ≠ 0 → a ≤ a * b`.

It's one way of saying that a divisor of a positive number
has to be at most that number.
-/
TheoremDoc MyNat.le_mul_right as "le_mul_right" in "≤"

Introduction
"
One day this game will have a Prime Number World, with a final boss
of proving that $2$ is prime.
To do this, we will have to rule out things like $2 = 37 × 42.$
We will do this by proving that any factor of $2$ is at most $2$,
which we will do using this lemma. The proof I have in mind manipulates the hypothesis
until it becomes the goal, using pretty much everything which we've proved in this world so far.
"

Statement le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  apply mul_left_ne_zero at h
  apply one_le_of_ne_zero at h
  apply mul_le_mul_right 1 b a at h
  rw [one_mul, mul_comm] at h
  exact h

Conclusion "Here's what I was thinking of:
```
apply mul_left_ne_zero at h
apply one_le_of_ne_zero at h
apply mul_le_mul_right 1 b a at h
rw [one_mul, mul_comm] at h
exact h
```
"
