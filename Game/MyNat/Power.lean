import Game.MyNat.Multiplication

namespace MyNat
open MyNat

opaque pow : ℕ → ℕ → ℕ

instance : Pow ℕ ℕ where
  pow := pow

-- notation a ^ b := pow a b

@[MyNat_decide]
axiom pow_zero (m : ℕ) : m ^ 0 = 1

@[MyNat_decide]
axiom pow_succ (m n : ℕ) : m ^ (succ n) = m ^ n * m

@[MyNat_decide]
theorem toNat_pow (m n : MyNat) : (m ^ n).toNat = m.toNat ^ n.toNat := by
  induction n <;> simp [MyNat_decide, *, Nat.pow_zero, Nat.pow_succ];

end MyNat
