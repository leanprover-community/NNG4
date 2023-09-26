import Game.Levels.Power.L08pow_pow

World "Power"
Level 9
Title "add_sq"

namespace MyNat

Introduction
"
[final boss music]

You see something written on the stone dungeon wall:
it seems to say that the ring hack in NNG3 doesn't work any more :-(

**TODO** fix this
"

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
In NNG3 the `ring` tactic did this level immediately. **TODO** make this work
in Lean 4!

It's all over! You have proved a theorem which has tripped up
schoolkids for generations (some of them think $(a+b)^2=a^2+b^2$).
If you did it using rewrites, how many did you use? I can do it in 12.
**TODO** link to source code?

If you didn't play the other worlds like even/odd world yet,
then feel free to try these next.

But wait! This boss is stirring...and mutating into a second more powerful form!
"
