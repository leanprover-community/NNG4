import Game.Metadata

example (a : ℕ) : a = 0 ∨ ¬ (a = 0) := by
  by_cases h : a = 0
  · left
    exact h
  · right
    -- here the goal should show `h : a ≠ 0`
    exact h

-- set_option pp.all true in
example (a : ℕ) : ¬ (a = 0) ↔ a ≠ 0 := by
  -- both should be displayed the same way
  rfl
