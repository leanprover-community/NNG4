import Game.Levels.Multiplication
import Game.MyNat.Division

World "Division"
Level 2
Title "dvd_refl"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that n ∣ n for any natural number n.
  In other words, 'divides' is a reflexive relation on the natural
  numebrs.

"
/-- `dvd_refl x` is a proof that `x ∣ x`.-/
TheoremDoc MyNat.dvd_refl as "dvd_refl" in "∣"

Statement dvd_refl
    (n : ℕ) :  n ∣ n := by
      use 1
      rw[mul_one]
      rfl

Conclusion
"
  Well Done, you have now proven that n|n , the next step is to prove that n|0.
"
