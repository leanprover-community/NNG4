import Game.Metadata

open MyNat

/-- `use` should not try `rfl` -/
example : ∃ n: ℕ, n = 3 := by
  use 3
  rfl

/-- Provide multiple values -/
example : ∃ n m : ℕ, n = m := by
  use 3, 3
  rfl
