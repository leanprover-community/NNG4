import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.Levels.Division.L08dvd_antisymm
import Game.MyNat.PeanoAxioms

World "Division"
Level 12
Title ""

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if a | b  and a ≠ b then ¬ (b ∣ a) for all a,b ∈ ℕ.
"
/-- `dvd_not_eq a b c` is a proof that if `a | b` and `a ≠ b` then `¬ (b ∣ a)` .-/
TheoremDoc MyNat.dvd_not_eq as "dvd_not_eq" in "∣"

Statement dvd_not_eq
  (a b : ℕ) (h1 : a ∣ b) (h2 : a ≠ b) : ¬ (b ∣ a) := by
  Hint "Start with intro"
  intro h
  apply h2
  Hint "Think about the theorems you have already proven and how they can be applied here"
  exact dvd_antisymm a b h1 h


Conclusion
"
  Congratulations, you have completed all the levels in divisibility world!
"
