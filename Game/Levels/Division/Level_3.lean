import Game.Levels.AdvMultiplication

World "Division"
Level 3
Title "div_antisymm"

namespace MyNat

Introduction
"

"

LemmaDoc MyNat.div_antisymm as "div_antisymm" in "∣" "
`div_antisymm a b` is a proof that `if a ∣ b and b ∣ a, then a = b`.
"

NewLemma MyNat.div_antisymm

Statement
    (a b : ℕ) (h1 : a ∣ b) (h2 : b ∣ a): a = b := by
  Hint "You will need to expand what `h1` and `h2` atually mean. You may find `rcases` helpful"
  rcases h1 with ⟨c, hc⟩
  rcases h2 with ⟨d , rfl⟩
  -- need to cancel b's:
  have : 1 = c * d
  -- need the fact that if 1 = cd, c = d = 1
  have : 1 = c
  rw [this] at hd -- hc : a = b
  exact hd

LemmaTab "∣"
