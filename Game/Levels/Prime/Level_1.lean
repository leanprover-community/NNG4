import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication.all_levels
import Game.MyNat.Division
import Game.MyNat.Prime


World "Prime"
Level 1
Title "prime_two"

LemmaTab "Prime"

namespace MyNat

----
def lt_myNat (a b : MyNat) := a ≤ b ∧ ¬ (b ≤ a)

instance : LT MyNat := ⟨lt_myNat⟩

theorem lt :  ∀ (a b : MyNat), a < b ↔ a ≤ b ∧ ¬b ≤ a := fun _ _ => Iff.rfl
----

Introduction
"
  In this level, we will prove that 2 is a prime number. For reference the definition of
  `Prime n` is that \"n ≥ 2 and if a ∣ n, then a = 1 or a = n.\"
"

LemmaDoc MyNat.prime_two as "prime_two" in "Prime" "
`prime_two` is a proof that 2 is prime.
"

lemma succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  have := zero_ne_succ a
  by_contra h
  have h' : 0 = succ a := by exact (Eq.symm h)
  contradiction

lemma dvd_two_leq_two (a : ℕ) (h : a ∣ 2) : a ≤ 2 := by
  match h with
  |⟨k, e⟩=>
  rw [e]
  have := le_mul_right a k ?_
  assumption
  rw [← e]
  rw [two_eq_succ_one]
  exact succ_ne_zero 1

lemma le_two (a : ℕ) (h : a ≤ 2) : a = 0 ∨ a = 1 ∨ a = 2 := by
  apply Or.elim (Classical.em (a = 2))
  · intro
    right
    right
    assumption
  · intro
    have h' : a ≤ 1 := by {
      sorry
    }
    have := le_one a h'
    apply Or.elim this
    · intro
      left
      assumption
    · intro
      right
      left
      assumption


  sorry

Statement prime_two :
  Prime 2 := by
  unfold Prime
  constructor
  use 0
  rw [add_zero]
  rfl
  intros a ha
  have : a ≤ 2 := by exact dvd_two_leq_two a ha
  have h : a = 0 ∨ a = 1 ∨ a = 2 := by sorry
  rcases h with ⟨h1, h2⟩
  · exfalso
    rcases ha with ⟨b, hb⟩
    rw [zero_mul] at hb
    cases hb
  · exact h

end MyNat
