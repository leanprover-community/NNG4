import Game.MyNat.Multiplication

namespace MyNat
open MyNat

opaque pow : ℕ → ℕ → ℕ

-- notation `a ^ b` for `pow a b`
instance : Pow ℕ ℕ where
  pow := pow

-- Note: since v4.2.0-rc2
macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : MyNat) ($y : MyNat))

@[MyNat_decide]
axiom pow_zero (m : ℕ) : m ^ 0 = 1

@[MyNat_decide]
axiom pow_succ (m n : ℕ) : m ^ (succ n) = m ^ n * m

end MyNat
