import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms

World "Division"
Level 7
Title "dvd_le"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if `a | b` and `b != 0` then `a <= b` for all a,b ∈ ℕ. In other words,
  we will prove that a number only divides number's greater than or equal to itself.
"
/-- `dvd_ls a b` is a proof that if `a | b` and `b != 0 `then `a <= b`.-/
TheoremDoc MyNat.dvd_le as "dvd_le" in "∣"

Statement dvd_le
    (a b : ℕ) (hab : a ∣ b) (hb : b ≠ 0) : a <= b := by
    cases hab with d hd
    rw[hd]
    apply le_mul_right
    rw[hd] at hb
    exact hb

Conclusion
"
My proof:
```
  cases hab with d hd
  rw[hd]
  apply le_mul_right
  rw[hd] at hb
  exact hb
```
"
