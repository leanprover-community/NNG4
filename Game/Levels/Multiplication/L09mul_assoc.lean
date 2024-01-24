import Game.Levels.Multiplication.L08add_mul


World "Multiplication"
Level 9
Title "mul_assoc"

namespace MyNat

Introduction
"
We now have enough to prove that multiplication is associative,
the boss level of multiplication world. Good luck!
"

TheoremDoc MyNat.mul_assoc as "mul_assoc" in "*" "
`mul_assoc a b c` is a proof that `(a * b) * c = a * (b * c)`.

Note that when Lean says `a * b * c` it means `(a * b) * c`.

Note that `(a * b) * c = a * (b * c)` cannot be proved by \"pure thought\":
for example subtraction is not associative, as `(6 - 2) - 1` is not
equal to `6 - (2 - 1)`.
"

/-- Multiplication is associative.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$(ab)c = a(bc)$. -/
Statement mul_assoc
    (a b c : ℕ) : (a * b) * c = a * (b * c)  := by
  induction c with d hd
  · rw [mul_zero, mul_zero, mul_zero]
    rfl
  · rw [mul_succ]
    rw [mul_succ]
    rw [hd]
    rw [mul_add]
    rfl

TheoremTab "*"

Conclusion "
A passing mathematician notes that you've proved
that the natural numbers are a commutative semiring.

If you want to begin your journey to the final boss, head for Power World.
"
