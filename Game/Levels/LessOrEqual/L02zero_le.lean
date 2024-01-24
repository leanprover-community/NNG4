import Game.Levels.LessOrEqual.L01le_refl

World "LessOrEqual"
Level 2
Title "0 ≤ x"

namespace MyNat

Introduction
"
To solve this level, you need to `use` a number `c` such that `x = 0 + c`.
"

LemmaDoc MyNat.zero_le as "zero_le" in "≤" "
`zero_le x` is a proof that `0 ≤ x`.
"

/-- If $x$ is a number, then $0 \le x$. -/
Statement zero_le (x : ℕ) : 0 ≤ x := by
  use x
  rw [zero_add]
  rfl

TheoremTab "≤"
