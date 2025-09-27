import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms

World "Division"
Level 4
Title "dvd_one"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if n ∣ 1 then n = 1 for all n ∈ ℕ. In other words,
  only one can divide one.
"
/-- `dvd_one n` is a proof that if `n | 1` then `n = 1`.-/
TheoremDoc MyNat.dvd_one as "dvd_one" in "∣"

Statement dvd_one
    (n : ℕ) : (h:  n ∣ 1 ) → n = 1 := by
    Hint "Start with `intro`"
    intro
    Hint "Now try `cases h with k h1`"
    cases h with k h1
    symm at h1
    apply mul_right_eq_one at h1
    exact h1


Conclusion
"
  Congratulations, you have now proven that the only number that can divide one is one.
"
