import Game.Levels.Multiplication
import Game.MyNat.Division
import Game.MyNat.Prime

World "Prime"
Level 1
Title "two_prime"

LemmaTab "Prime"

namespace MyNat

Introduction
"
  In this level, we will prove that 2 is a prime number. For reference the defition of
  `Prime n` is that \"n ≥ 2 and if n ∣ a * b then n ∣ a or n ∣ b."
"

LemmaDoc MyNat.two_prime as "two_prime" in "Prime" "
`one_div x` is a proof that `1 ∣ x`.
"

Statment two_prime
  Prime 2 := by sorry

end MyNat
