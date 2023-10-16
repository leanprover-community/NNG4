import Game.Levels.AdvMultiplication


World "Division"
Level 1
Title "one_div"

Introduction
"
  In this section, we will prove that 1 ∣ n for all n ∈ ℕ.
"

Statement
    (n : ℕ) : 1 ∣ n := by
  use n

Conclusion
"

"
