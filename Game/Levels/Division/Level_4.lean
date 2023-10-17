import Game.Levels.AdvMultiplication

World "Division"
Level 4
Title "div_trans"

namespace MyNat

Introduction
"
  In this section, we will prove that ∣ is transitive. This will complete the proof that ∣ is a
  partial order on ℕ.
"

LemmaDoc MyNat.div_trans as "div_trans" in "∣" "
`div_trans a b c` is a proof that `a ∣ b ∧ b ∣ c → a ∣ c`.
"

NewLemma MyNat.div_trans

Statement
    (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  Hint "Here, like the last level, you may find `rcases` helpful."
  rcases hbc with ⟨m, hm⟩
  rcases hab with ⟨n, rfl⟩

  -- b = na, c = mb
  -- c = mna
  Hint "Now, since we are looking show `a ∣ c`, which is an existience hypothesis, a `use` tactic
  would be a good choice."
  use (m * n)
  assumption

LemmaTab "∣"
