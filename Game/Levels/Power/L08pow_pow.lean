import Game.Levels.Power.L07mul_pow

World "Power"
Level 8
Title "pow_pow"

namespace MyNat

Introduction
"
One of the best named levels in the game, a savage `pow_pow`
sub-boss appears as the music reaches a frenzy. What
else could there be to prove about powers after this?
"

LemmaDoc MyNat.pow_pow as "pow_pow" in "Pow" "
`pow_pow a m n` is a proof that $(a^m)^n=a^{mn}.$
"

/-- For all naturals $a$, $m$, $n$, we have $(a ^ m) ^ n = a ^ {mn}$. -/
Statement pow_pow
    (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with t Ht
  · rw [mul_zero, pow_zero, pow_zero]
    rfl
  · rw [pow_succ, Ht, mul_succ, pow_add]
    rfl

LemmaTab "Pow"

-- **TODO** if these are `simp` then they should be `simp`ed at source.
attribute [simp] MyNat.pow_zero
attribute [simp] MyNat.pow_succ
attribute [simp] MyNat.pow_one
attribute [simp] MyNat.one_pow
attribute [simp] MyNat.pow_pow -- yes or no?

Conclusion
"
The music dies down. Is that it?

Course it isn't, you can
clearly see that there are two worlds left.

A passing mathematician says that mathematicians don't have a name
for the structure you just constructed. You feel cheated.

Suddenly the music starts up again. This really is the final boss.
"
