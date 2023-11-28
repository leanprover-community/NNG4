import Game.Levels.Power.L02zero_pow_succ

World "Power"
Level 3
Title "pow_one"

namespace MyNat

LemmaDoc MyNat.pow_one as "pow_one" in "^" "
`pow_one a` says that `a ^ 1 = a`.

Note that this is not quite true by definition: `a ^ 1` is
defined to be `a ^ 0 * a` so it's `1 * a`, and to prove
that this is equal to `a` you need to use induction somewhere.
"
/-- For all naturals $a$, $a ^ 1 = a$. -/
Statement pow_one (a : ℕ) : a ^ 1 = a  := by
  rw [one_eq_succ_zero]
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]
  rfl

LemmaTab "^"
