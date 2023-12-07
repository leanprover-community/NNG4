import Game.Levels.Division.Level_3

World "Division"
Level 4
Title "dvd_trans"

namespace MyNat

Introduction
"
  In this level, we will prove that ∣ is transitive. That is, if
  `a ∣ b` and `b ∣ c`, then `a ∣c ` This will complete the proof
  that ∣ is a partial order on ℕ.
"

LemmaDoc MyNat.dvd_trans as "dvd_trans" in "∣" "
`div_trans a b c` is a proof that `a ∣ b ∧ b ∣ c → a ∣ c`.
"

Statement dvd_trans
    (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  Hint "Here, like the last level, you may find `rcases` helpful."
  rcases hbc with ⟨m, hm⟩
  rcases hab with ⟨n, rfl⟩
  Hint "Now, since we are looking show `a ∣ c`, which is an existience hypothesis, the `use`
  tactic would be a good choice."
  use (m * n)
  Hint "Now the goal is clear, its just a case of finding the correct rewrites."
  rw [hm]
  rw [mul_assoc]
  rw [mul_comm n m]
  rfl

Conclusion
"
  Great work. We have succedfully proven that `∣` is a partial order on ℕ.
"

LemmaTab "∣"
