import Game.Levels.LessOrEqual

namespace MyNat

example (P Q : Prop) (h : P ∨ Q) : False := by
  cases h with hp hq
  · sorry -- hp : P
  · sorry -- hq : Q

example (a b : ℕ) (h : a ≤ b) : False := by
  cases h with c hc
  -- hc: b = a + c
  sorry

-- not working yet
example (a : ℕ) : a = a := by
  cases a with d
  -- get MyNat.zero because we used rec not rec' :-(
  · sorry
  · sorry
