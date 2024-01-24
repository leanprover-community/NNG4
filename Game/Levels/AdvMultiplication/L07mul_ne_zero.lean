import Game.Levels.AdvMultiplication.L06mul_right_eq_one

World "AdvMultiplication"
Level 7
Title "mul_ne_zero"

TheoremTab "*"

namespace MyNat

LemmaDoc MyNat.mul_ne_zero as "mul_ne_zero" in "*" "
`mul_ne_zero a b` is a proof that if `a ≠ 0` and `b ≠ 0` then `a * b ≠ 0`.
"

Introduction
"
This level proves that if `a ≠ 0` and `b ≠ 0` then `a * b ≠ 0`. One strategy
is to write both `a` and `b` as `succ` of something, deduce that `a * b` is
also `succ` of something, and then `apply zero_ne_succ`.
"

Statement mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  Hint (hidden := true) "Start with `apply eq_succ_of_ne_zero at ha` and `... at hb`"
  apply eq_succ_of_ne_zero at ha
  apply eq_succ_of_ne_zero at hb
  cases ha with c hc
  cases hb with d hd
  rw [hc, hd]
  rw [mul_succ, add_succ]
  symm
  apply zero_ne_succ
