import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms

World "Division"
Level 5
Title "dvd_trans"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if a | b and b | c then a | c for all a,b,c ∈ ℕ. In other words,
  we will prove the transitivity of division.
"
/-- `dvd_trans a b c` is a proof that if `a | b` and `b | c `then `a | c`.-/
TheoremDoc MyNat.dvd_trans as "dvd_trans" in "∣"

Statement dvd_trans
    (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  Hint "Here, like the last level, you may find `cases` helpful."
  cases hbc with m hm
  cases hab with n hn
  Hint "Now, since we are looking show `a ∣ c`, which is an existience hypothesis, the `use`
  tactic would be a good choice."
  rw[hn] at hm
  Hint "Now the goal is clear, its just a case of finding the correct rewrites."
  use (n * m)
  rw [← mul_assoc]
  exact hm


Conclusion
"
  Congratulations, you have now proven that division is transitive!
"
