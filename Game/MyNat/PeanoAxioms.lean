import Game.MyNat.Definition
import Mathlib.Tactic

namespace MyNat

-- KB note: I have not thought about simp at all and perhaps this
-- comes from some earlier NNG3 port?
attribute [-simp] MyNat.succ.injEq
-- example (a b : ℕ) (h : (succ a) = b) : succ (succ a) = succ b := by
--   simp
--   sorry

def pred : ℕ → ℕ
| 0 => 37
| succ n => n

lemma pred_succ (n : ℕ) : pred (succ n) = n := rfl

theorem succ_inj (a b : ℕ) (h : succ a = succ b) : a = b := by
  rw [← pred_succ a, h, pred_succ]

def is_zero : ℕ → Prop
| 0 => True
| succ n => False

lemma is_zero_zero : is_zero 0 = True := rfl
lemma is_zero_succ (n : ℕ) : is_zero (succ n) = False := rfl

theorem zero_ne_succ (a : ℕ) : 0 ≠ succ a := by
  intro h
  rw [← is_zero_succ a]
  rw [← h]
  rw [is_zero_zero]
  trivial
