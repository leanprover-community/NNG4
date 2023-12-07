import Game.Levels.Division.Level_4

World "Division"
Level 5
Title "dvd_mul_right"

LemmaTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if d ∣ a, then d ∣ ab.
"

LemmaDoc MyNat.dvd_mul_right as "dvd_mul_right" in "∣" "
`div_a_div_ab d a b` is a proof that `d ∣ a → d ∣ a * b`.
"

Statement dvd_mul_right
    (d a b : ℕ) (hd : d ∣ a) : d ∣ (a * b) := by
  Hint "You are probably getting the hang of the start of these proofs by now! Try `rcases`."
  rcases hd with ⟨k, hk⟩
  Hint "Since the Goal is an exists statment, `use` will be a good choice."
  use (k * b)
  Hint "The goal is pretty trivial now, you just need to figure out the correct sequence of
  rewrites to finish the job."
  rw [hk]
  rw [mul_assoc]
  rfl
