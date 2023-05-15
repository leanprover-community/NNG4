import Game.MyNat.Addition

namespace MyNat

open MyNat

def mul : MyNat → MyNat → MyNat
  | _, 0   => 0
  | a, b + 1 => (MyNat.mul a b) + a

instance : Mul MyNat where
  mul := MyNat.mul


theorem mul_zero (a : MyNat) : a * 0 = 0 := by rfl

theorem mul_succ (a b : MyNat) : a * (succ b) = a * b + a := by rfl
