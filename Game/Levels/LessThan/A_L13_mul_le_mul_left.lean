import Game.Levels.LessThan.A_L12_succ_lt_succ_iff
import Game.Levels.Multiplication

World "LessThan"
Level 13
Title "mul_le_mul_left"

TheoremTab "≤" --should this be ≤?

namespace MyNat

/-- `mul_le_mul_left a b c` is a proof that if `a ≤ b` then a * c ≤ b * c -/
TheoremDoc MyNat.mul_le_mul_left as "mul_le_mul_left" in "≤" 

Introduction "We prove that we can multiply both sides of a `≤`
proposition by a natural number and retain a valid `≤` proposition."

--note to Kevin, I removed the requirement that `0 ≤ c`, since that always
--happens, and I think keeping it is a little confusing.
--If some of the instances need this, then I suppose we could use
--this theorem as a base and use `zero_le c`.


Statement mul_le_mul_left (a b c: ℕ)
    : a ≤ b → a * c ≤ b * c := by
  intro h0
  cases h0 with n hab
  Hint"What number is equal to `{b} * {c} - {a} * {c}'?"
  use (c * n)

  rw [hab,add_mul,mul_comm n c]
  rfl

Conclusion "
My Proof:
```
intro h0
cases h0 with n hab
use (c * n)
rw [hab,add_mul_mul_comm n c]
rfl
```
"
