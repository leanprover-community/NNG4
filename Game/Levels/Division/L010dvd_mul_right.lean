import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms

World "Division"
Level 10
Title ""

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if a | b  then a | b*c for all a,b,c ∈ ℕ.
"
/-- `dvd_mul_right a b c` is a proof that if `a | b` then `a | b*c` .-/
TheoremDoc MyNat.dvd_mul_right as "dvd_mul_right" in "∣"

Statement dvd_mul_right
    (a b c : ℕ) (h1 : a ∣ b) : a ∣ b*c := by
  cases h1 with k1 h11
  use k1*c
  rw [<- mul_assoc]
  rw [h11]
  rfl




Conclusion
"
  Congratulations!
"
