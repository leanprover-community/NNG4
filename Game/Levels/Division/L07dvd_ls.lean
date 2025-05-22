import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms

World "Division"
Level 7
Title "dvd_ls"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if a | b and b != 0 then a <=b for all a,b ∈ ℕ. In other words,
  we will prove that a number only divides number's greater than or equal to itself.
"
/-- `dvd_ls a b` is a proof that if `a | b` and `b != 0 `then `a <= b`.-/
TheoremDoc MyNat.dvd_ls as "dvd_ls" in "∣"

Statement dvd_ls
    (a b : ℕ) (hab : a ∣ b) (hb : b ≠ 0) : a <= b := by
    cases hab with k
    rw[h]
    apply le_mul_right
    rw[h] at hb
    exact hb

Conclusion
"
  Congratulations!
"
