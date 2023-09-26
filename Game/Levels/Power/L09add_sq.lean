import Game.Levels.Power.L08pow_pow

World "Power"
Level 9
Title "add_sq"

namespace MyNat

Introduction
"
[final boss music]
"

-- **TODO** get the `ring` hack working again.

LemmaDoc MyNat.add_sq as "add_sq" in "Pow" "
`add_sq a b` is the statment that $(a+b)^2=a^2+b^2+2ab.$
"

/-- For all naturals $a$ and $b$, we have
$$(a+b)^2=a^2+b^2+2ab.$$ -/
Statement add_sq
    (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [pow_two, pow_two, pow_two]
  rw [add_right_comm]
  rw [mul_add, add_mul, add_mul]
  rw [two_mul, add_mul]
  rw [mul_comm b a]
  rw [← add_assoc, ← add_assoc]
  rfl

LemmaTab "Pow"

Conclusion
"
It's all over! You have proved a theorem which has tripped up
schoolkids for generations (some of them think $(a+b)^2=a^2+b^2$:
this is \"the freshman's dream\").

How many rewrites did you use? I can do it in 12.
**DEPLOY_TODO** link to source code when I have stable internet

But wait! This boss is stirring...and mutating into a second more powerful form!
"

-- *TODO* add something like this when the new worlds are written
-- If you didn't play the other worlds like even/odd world yet,
-- then feel free to try these next.
