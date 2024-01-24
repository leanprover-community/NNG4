import Game.Levels.Power.L06pow_add

World "Power"
Level 7
Title "mul_pow"

namespace MyNat

Introduction
"
The music gets ever more dramatic, as we explore
the interplay between exponentiation and multiplication.

If you're having trouble exchanging the right `x * y`
because `rw [mul_comm]` swaps the wrong multiplication,
then read the documentation of `rw` for tips on how to fix this.
"

/-- `mul_pow a b n` is a proof that $(ab)^n=a^nb^n.$ -/
TheoremDoc MyNat.mul_pow as "mul_pow" in "^"

/-- For all naturals $a$, $b$, $n$, we have $(ab) ^ n = a ^ nb ^ n$. -/
Statement mul_pow
    (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with t Ht
  · rw [pow_zero, pow_zero, pow_zero, mul_one]
    rfl
  · rw [pow_succ, pow_succ, pow_succ, Ht]
    -- simp
    repeat rw [mul_assoc]
    rw [mul_comm a (_ * b), mul_assoc, mul_comm b a]
    rfl

TheoremTab "^"
