import Game.Levels.AdvMultiplication

World "Division"
Level 2
Title "div_refl"

Introduction
"
  In this section, we will prove that n ∣ n for any natural number n. In other words, 'divides' is
  a reflexive relation on the natural numebrs.
"

Statement
    (n : ℕ) : n ∣ n := by
  use 1
  rfl

Conclusion
"

"
