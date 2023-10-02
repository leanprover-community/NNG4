import Game.MyNat.Addition
import Mathlib.Tactic

namespace MyNat

-- KB note: I have not thought about simp at all and perhaps this
-- comes from some earlier NNG3 port?
attribute [-simp] MyNat.succ.injEq
-- example (a b : ℕ) (h : (succ a) = b) : succ (succ a) = succ b := by
--   simp
--   sorry

theorem succ_inj (a b : ℕ) : succ a = succ b → a = b := by rintro ⟨h⟩; rfl

theorem zero_ne_succ (a : ℕ) : 0 ≠ succ a := by rintro ⟨h⟩
