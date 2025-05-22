import Game.Levels.Multiplication
import Game.MyNat.Division

World "Division"
Level 3
Title "dvd_zero"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that n ∣ 0 for all n ∈ ℕ. In other words,
  zero can be divided by any number.
"
/-- `dvd_zero x` is a proof that `x | 0 `.-/
TheoremDoc MyNat.dvd_zero as "dvd_zero" in "∣"

Statement dvd_zero
    (n : ℕ) :  n ∣ 0 := by
      use 0
      rw[mul_zero]
      rfl

Conclusion
"
  Congratulations!
"
