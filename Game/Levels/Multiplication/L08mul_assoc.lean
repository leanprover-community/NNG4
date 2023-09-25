import Game.Levels.Multiplication.L07add_mul


World "Multiplication"
Level 8
Title "mul_assoc"

namespace MyNat

Introduction
"
We now have enough to prove that multiplication is associative.
"

/-- Multiplication is associative.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$(ab)c = a(bc)$. -/
Statement MyNat.mul_assoc
    (a b c : ℕ) : (a * b) * c = a * (b * c)  := by
  induction c with d hd
  · rw [mul_zero, mul_zero, mul_zero]
    rfl
  · rw [mul_succ]
    rw [mul_succ]
    rw [hd]
    rw [mul_add]
    rfl

LemmaTab "Mul"

Conclusion "
  A passing mathematician notes that you've proved
  that the natural numbers are a commutative semiring.
"
