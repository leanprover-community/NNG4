import Game.MyNat.Multiplication

namespace MyNat
open MyNat

opaque pow : ℕ → ℕ → ℕ

instance : Pow ℕ ℕ where
  pow := pow

-- notation a ^ b := pow a b

axiom pow_zero (m : ℕ) : m ^ 0 = 1

axiom pow_succ (m n : ℕ) : m ^ (succ n) = m ^ n * m

end MyNat
