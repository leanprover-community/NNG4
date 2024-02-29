import Game.Tactic.Induction
import Game.MyNat.Addition
import Mathlib.Tactic.Have
import Mathlib.Tactic

example (a b : ℕ) : a + b = a → b = 0 := by
  induction b with d hd
  · /-
    a : ℕ
    ⊢ a + 0 = a → 0 = 0
    -/
    sorry
  · sorry

example (a b c : ℕ) (g : c = 0) : a + b = a → b = 0 := by
  intro h -- h : a + b = a
  induction b with d hd generalizing g
  · /-
    a b: ℕ
    h✝ : a + b = a
    h : a + 0 = a
    ⊢ 0 = 0
    -/
    sorry
  · /-
    case succ
    a c d : ℕ
    hd : c = 0 → a + d = a → d = 0
    g : c = 0
    h : a + MyNat.succ d = a
    ⊢ MyNat.succ d = 0
    -/
    sorry
