import Game.Levels.Power.L03pow_one

World "Power"
Level 4
Title "one_pow"

namespace MyNat

LemmaDoc MyNat.one_pow as "one_pow" in "^" "
`one_pow n` is a proof that $1^n=1$.
"
/-- For all naturals $m$, $1 ^ m = 1$. -/
Statement one_pow
    (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with t ht
  · rw [pow_zero]
    rfl
  · rw [pow_succ]
    rw [ht]
    rw [mul_one]
    rfl

TheoremTab "^"
