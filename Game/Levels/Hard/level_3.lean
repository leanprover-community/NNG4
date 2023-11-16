import Game.Levels.Hard.level_2


World "Hard"
Level 3
Title "Golbach"

LemmaTab "Hard"

namespace MyNat

Introduction
"
  The Golbach conjecture, first posed in 1792 in a letter to Euler states that every
  natural number greater than 2 is the sum of two prime numbers. It remains unproven
  to this day, but has been checked for all naturals up to 4 x 10¹⁸.
"

LemmaDoc MyNat.Golbach as "Golbach" in "Hard" "
`Golbach` is the proof of disproof of the Golbach conjecture.
"

Statement Golbach : (∀ n : ℕ), n ≥ 2 → (∃ a b : ℕ), (Prime a) ∧ (Prime b) ∧ (n = a + b) := by
  sorry
