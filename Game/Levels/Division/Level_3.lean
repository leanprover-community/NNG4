
World "Division"
Level 3
Title "div_ne"


Statement
    (a b : ℕ) (h : a ≠ b) : a ∣ b → ¬ b ∣ a := by
  intros hab, hba
  match hab, hba with
  |⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩ =>
  rewrite hk₂ at hk₁
  -- b = k₁k₂b
  -- we now need to cancel `b` on both sides
  have hk : 1 = k₁ * k₂ := by sorry
  -- we need the fact that if xy = 1, then x = y = 1:
  have : 1 = k₁ := by sorry
  rewrite this at hk₁
  contradiction

  Conclusion
  "

  "
