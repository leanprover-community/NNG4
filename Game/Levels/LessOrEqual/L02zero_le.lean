import Game.Levels.LessOrEqual.L01le_refl

World "LessOrEqual"
Level 2
Title "0 ≤ x"

namespace MyNat

Introduction
"
Although subtraction doesn't make sense for general numbers in this game
(because there are no negative numbers in this game), one way of thinking about
how to prove `a ≤ b` is to `use b - a`. See how you get on with this level,
which proves that every number in the game is at least 0.
"

/-- If $x$ is a number, then $0 \\le x$. -/
Statement le_refl (x : ℕ) : 0 ≤ x := by
  use x
  rw [zero_add]
  rfl

LemmaTab "≤"
