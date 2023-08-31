import Game.MyNat.Addition

namespace MyNat

attribute [-simp] MyNat.succ.injEq
example (a b : ℕ) (h : (succ a) = b) : succ (succ a) = succ b := by
  -- `simp` here makes no progress
  sorry

axiom succ_inj {a b : ℕ} : succ a = succ b → a = b

axiom zero_ne_succ (a : ℕ) : 0 ≠ succ a
