import Game.Levels.LessOrEqual
import Game.Levels.Multiplication

World "AdvMultiplication"
Level 1
Title "mul_le_mul_right"

TheoremTab "*"

namespace MyNat

TheoremDoc MyNat.mul_le_mul_right as "mul_le_mul_right" in "*" "
`mul_le_mul_right a b t` is a proof that `a ≤ b → a * t ≤ b * t`.
"

Introduction
"Let's warm up with an easy one, which works even if `t = 0`."

Statement mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  cases h with d hd
  use d * t
  rw [hd, add_mul]
  rfl

Conclusion
"My proof:
```
cases h with d hd
use d * t
rw [hd, add_mul]
rfl
```
"
