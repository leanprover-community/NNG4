import Game.Tactic.Cases
import Game.MyNat.Inequality

namespace MyNat

example (P Q : Prop) (h : P ∨ Q) : False := by
  cases h with hp hq
  · /-
    case inl
    P Q : Prop
    hp : P
    ⊢ False
    -/
    sorry
  · /-
    case inr
    P Q : Prop
    hq : Q
    ⊢ False
    -/
    sorry

example (a b : ℕ) (h : a ≤ b) : False := by
  cases h with c hc
  /-
  case intro
  a b c : ℕ
  hc : b = a + c
  ⊢ False
  -/
  sorry

example (a : ℕ) : a = a := by
  cases a with d
  · /-
    case zero
    ⊢ 0 = 0
    -/
    sorry
  · sorry
