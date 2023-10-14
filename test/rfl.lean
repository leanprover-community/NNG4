import Game.Tactic.Rfl

/- Custom `rfl` should close `A ↔ A`. -/
example (A : Prop) : A ↔ A := by
  rfl
