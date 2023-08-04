import Game.MyNat.Definition

namespace MyNat

open MyNat

def add : MyNat → MyNat → MyNat
  | a, 0   => a
  | a, MyNat.succ b => MyNat.succ (MyNat.add a b)

instance : Add MyNat where
  add := MyNat.add

/--
If `a` is a natural number, then `add_zero a` is the proof that `a + 0 = a`.
-/
theorem add_zero (a : MyNat) : a + 0 = a := by rfl

/--
If `a` and `d` are natural numbers, then `add_succ a d` is the proof that
`a + succ d = succ (a + d)`.
-/
theorem add_succ (a d : MyNat) : a + (succ d) = succ (a + d) := by rfl
