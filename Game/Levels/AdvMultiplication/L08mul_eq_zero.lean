import Game.Levels.AdvMultiplication.L07mul_ne_zero

World "AdvMultiplication"
Level 8
Title "mul_eq_zero"

TheoremTab "*"

namespace MyNat

TheoremDoc MyNat.mul_eq_zero as "mul_eq_zero" in "*" "
`mul_eq_zero a b` is a proof that if `a * b = 0` then `a = 0` or `b = 0`.
"

Introduction
"
This level proves that if `a * b = 0` then `a = 0` or `b = 0`. It is
logically equivalent to the last level, so there is a very short proof.
"

Statement mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  Hint (hidden := true) "Start with `have h2 := mul_ne_zero a b`."
  have h2 := mul_ne_zero a b
  Hint (hidden := true) "Now the goal can be deduced from `h2` by pure logic, so use the `tauto`
  tactic."
  tauto
