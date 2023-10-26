import Game.Levels.Division.Level_2
import Game.Levels.AdvMultiplication.all_levels

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
  rw [hd] at hc
  by_cases hb : b = 0
  · rw [hb] at hd
    rw [zero_mul] at hd
    rw [hd, hb]
    rfl
  rw [mul_assoc] at hc
  have := self_eq_mul_right _ _ hc hb
  apply eq_one_of_mul_right_eq_one at this
  rw [this, mul_one] at hd
  exact hd

LemmaTab "∣"
