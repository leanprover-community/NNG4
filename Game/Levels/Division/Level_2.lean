import Game.Levels.Division.Level_1

World "Division"
Level 2
Title "dvd_refl"

LemmaTab "∣"

namespace MyNat

Introduction
"
  In this section, we will prove that n ∣ n for any natural number n. In other words, 'divides' is
  a reflexive relation on the natural numebrs.
"

LemmaDoc MyNat.dvd_refl as "dvd_refl" in "∣" "
`div_refl x` is a proof that `x ∣ x`.
"

Statement dvd_refl
    (n : ℕ) : n ∣ n := by
  Hint "This is true because `n = n * 1`"
  use 1
  rw [mul_one]
  rfl
