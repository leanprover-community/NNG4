import Game.MyNat.Addition

namespace MyNat

opaque mul : MyNat → MyNat → MyNat

instance : Mul MyNat where
  mul := MyNat.mul

@[MyNat_decide]
axiom mul_zero (a : MyNat) : a * 0 = 0

@[MyNat_decide]
axiom mul_succ (a b : MyNat) : a * (succ b) = a * b + a

-- @[MyNat_decide]
-- theorem toNat_mul (m n : MyNat) : (m * n).toNat = m.toNat * n.toNat := by
--   induction n <;> simp [MyNat_decide, *, Nat.mul_succ];
