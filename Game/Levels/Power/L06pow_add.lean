import Game.Levels.Power.L05pow_two

World "Power"
Level 6
Title "pow_add"

namespace MyNat

Introduction "Let's now begin our approach to the final boss,
by proving some more subtle facts about powers."

LemmaDoc MyNat.pow_add as "pow_add" in "^" "

`pow_add a m n` is a proof that $a^{m+n}=a^ma^n.$
"

/-- For all naturals $a$, $m$, $n$, we have $a^{m + n} = a ^ m  a ^ n$. -/
Statement pow_add
    (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with t ht
  · rw [add_zero, pow_zero, mul_one]
    rfl
  · rw [add_succ, pow_succ, pow_succ, ht, mul_assoc]
    rfl

LemmaTab "^"
