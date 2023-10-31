import Game.MyNat.Definition

namespace MyNat

opaque add : MyNat → MyNat → MyNat

instance instAdd : Add MyNat where
  add := MyNat.add

/--
`add_zero a` is a proof of `a + 0 = a`.

`add_zero` is a `simp` lemma, because if you see `a + 0`
you usually want to simplify it to `a`.
-/
@[simp]
axiom add_zero (a : MyNat) : a + 0 = a

/--
If `a` and `d` are natural numbers, then `add_succ a d` is the proof that
`a + succ d = succ (a + d)`.
-/
axiom add_succ (a d : MyNat) : a + (succ d) = succ (a + d)
