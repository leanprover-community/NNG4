import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication.all_levels
import Game.MyNat.Division
import Game.MyNat.Prime


World "Prime"
Level 1
Title "prime_two"

LemmaTab "Prime"

namespace MyNat

Introduction
"
  In this level, we will prove that 2 is a prime number. For reference the definition of
  `Prime n` is that \"n ≥ 2 and if a ∣ n, then a = 1 or a = n.\"
"

LemmaDoc MyNat.prime_two as "prime_two" in "Prime" "
`prime_two` is a proof that 2 is prime.
"

Statement prime_two :
  Prime 2 := by
  Hint "You may want to know what `Prime 2` actually means. For this, you can use
  `unfold Prime`."
  unfold Prime
  Hint "Use `constructor` to split up the `∧` statment into two goals."
  constructor
  use 0
  rw [add_zero]
  rfl
  Hint "You have done the easy half, now for the tough part."
  intros a ha
  have : a ≤ 2 := by exact dvd_two_leq_two a ha
  have h : a = 0 ∨ a = 1 ∨ a = 2 := by exact le_two a this
  rcases h with ⟨h1, h2⟩
  · exfalso
    rcases ha with ⟨b, hb⟩
    rw [zero_mul] at hb
    cases hb
  · exact h


end MyNat
