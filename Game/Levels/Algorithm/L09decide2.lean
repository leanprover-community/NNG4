import Game.Levels.Algorithm.L08decide

World "Algorithm"
Level 9
Title "decide again"

LemmaTab "Peano"

namespace MyNat

Introduction
"
We gave a pretty unsatisfactory proof of `2 + 2 ≠ 5` earlier on; now give a nicer one.
"

/-- $2+2 \neq 5.$ -/
Statement : (2 : ℕ) + 2 ≠ 5 := by
  try simp only [MyNat_decide]
  try decide

Conclusion "Congratulations! You've finished Algorithm World. These algorithms
will be helpful for you in Even-Odd World."
