import Game.Levels.AdvMultiplication

World "Division"
Level 5
Title "div_a_div_ab"

namespace MyNat

Introduction
"
  In this section, we will prove that if d ∣ a, then d ∣ ab.
"

LemmaDoc MyNat.div_a_div_ab as "div_a_div_ab" in "∣" "
`div_a_div_ab d a b` is a proof that `d ∣ a → d ∣ a * b`.
"

NewLemma MyNat.div_a_div_ab

Statement
    (d a b : ℕ) (hd : d ∣ a) : d ∣ (a * b) := by
  Hint "You are probably getting the hang of the start of these proofs by now! Try `rcases`."
  rcases hd with ⟨k, hk⟩
  -- a = kd
  Hint "Since the Goal is an exists statment, `use` will be a good choice."
  use (k * b)

  rw [hk]
  rw [Nat.add_comm d b]
  rfl

LemmaTab "∣"
