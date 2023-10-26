import Game.Levels.Division.Level_2

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

Statement div_antisymm
    (a b : ℕ) (h1 : a ∣ b) (h2 : b ∣ a): a = b := by
  Hint "You will need to expand what `h1` and `h2` atually mean. You may find `rcases` helpful"
  rcases h1 with ⟨c, hc⟩
  rcases h2 with ⟨d, hd⟩
  -- need to cancel b's:
  have hcd : b = b * d * c := by sorry
  have h1dc : 1 = d * c := by sorry
  -- need the fact that if 1 = dc, c = d = 1
  have h1c : 1 = c := by sorry
  rw [← h1c] at hc -- hc : a = b
  rw [mul_one] at hc
  exact Eq.symm hc

LemmaTab "∣"
