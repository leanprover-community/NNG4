import Game.MyNat.Multiplication

namespace MyNat
open MyNat

opaque pow : ℕ → ℕ → ℕ

-- notation `a ^ b` for `pow a b`
instance : Pow ℕ ℕ where
  pow := pow

@[MyNat_decide]
axiom pow_zero (m : ℕ) : m ^ 0 = 1

@[MyNat_decide]
axiom pow_succ (m n : ℕ) : m ^ (succ n) = m ^ n * m

end MyNat
