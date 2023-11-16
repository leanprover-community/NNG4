import Game.Levels.Hard.level_3


World "Hard"
Level 3
Title "Twin Prime"

LemmaTab "Hard"

namespace MyNat

Introduction
"
  A twin prime is a pair of primes (2, 3), (41, 43) etc. that are 2 apart. The conjecture
  states that there are infinitley many such pairs.
"

LemmaDoc MyNat.Twin_Prime as "Twin_Prime" in "Hard" "
`Twin_Prime` is the proof of the Twin Prime conjecture.
"

Statement Twin_Prime :
  (∀ M : ℕ), (∃ a b : ℕ), (a ≥ M) ∧ (b ≥ M) ∧ (a + 2 = b) ∧ (Prime a) ∧ (Prime b) := by sorry
