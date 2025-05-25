import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms

World "Division"
Level 12
Title ""

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if a | b  then a | c*b for all a,b,c ∈ ℕ.
"
/-- `dvd_mul_left a b c` is a proof that if `a | b` then `a | c*b` .-/
TheoremDoc MyNat.dvd_mul_left as "dvd_mul_left" in "∣"

Statement dvd_mul_left
    (a b c : ℕ) (h1 : a ∣ b) : a ∣ c*b := by
  cases h1 with k1 h11
  use k1*c
  rw [<- mul_assoc]
  rw [h11]
  rw [mul_comm]
  rfl
