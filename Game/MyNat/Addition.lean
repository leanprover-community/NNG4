import Game.MyNat.Definition

namespace MyNat

open MyNat

def add : MyNat → MyNat → MyNat
  | a, zero  => a
  | a, MyNat.succ b => MyNat.succ (MyNat.add a b)

instance instAdd : Add MyNat where
  add := MyNat.add

/--
`add_zero a` is a proof of `a + 0 = a`.

`add_zero` is a `simp` lemma, because if you see `a + 0`
you usually want to simplify it to `a`.
-/
@[simp] theorem add_zero (a : MyNat) : a + 0 = a := by rfl

/--
This theorem proves that (a + (d + 1)) = ((a + d) + 1) for a,d in MyNat.
-/
theorem add_succ (a d : MyNat) : a + (succ d) = succ (a + d) := by rfl
