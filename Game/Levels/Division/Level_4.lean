import Game.Levels.AdvMultiplication

World "Division"
Level 4
Title "div_trans"

Introduction
"
  In this section, we will prove that ∣ is transitive. This will complete the proof that ∣ is a
  partial order on ℕ.
"

Statement
    (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  match hab, hbc with
  |⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩ =>
  -- b = k₁a, c = k₂b
  rewrite hk₁ at hk₁
  -- c = k₂k₁a
  use (k₂ * k₁)
  assumption

Conclusion
"

"
