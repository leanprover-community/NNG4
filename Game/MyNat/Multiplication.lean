import Game.MyNat.Addition

namespace MyNat

opaque mul : MyNat → MyNat → MyNat

instance : Mul MyNat where
  mul := MyNat.mul

axiom mul_zero (a : MyNat) : a * 0 = 0

axiom mul_succ (a b : MyNat) : a * (succ b) = a * b + a
