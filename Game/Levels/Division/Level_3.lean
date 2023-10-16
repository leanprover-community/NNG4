import Game.Levels.AdvMultiplication

World "Division"
Level 3
Title "div_antisymm"

namespace MyNat

Introduction
"

"

LemmaDoc MyNat.div_antisymm as "div_antisymm" in "∣" "
`div_antisymm a b` is a proof that `if a ∣ b and b ∣ a, then a = b`.
"

NewLemma MyNat.div_ne

Statement
    (a b : ℕ) (h1 : a ∣ b) (h2 : b ∣ a): a = b := by
  /-intros hab, hba
  match hab, hba with
  |⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩ =>
  rewrite hk₂ at hk₁
  -- b = k₁k₂b
  -- we now need to cancel `b` on both sides
  have hk : 1 = k₁ * k₂ := by sorry
  -- we need the fact that if xy = 1, then x = y = 1:
  have : 1 = k₁ := by sorry
  rewrite this at hk₁
  contradiction-/

LemmaTab "∣"
