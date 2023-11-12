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

lemma le_cancel (a b t : ℕ) (h : a + t ≤ b + t) : a ≤ b := by
  match h with
  |⟨k, hk⟩ =>
  rw [add_assoc, add_comm t k, ← add_assoc] at hk
  have : b = a + k := by exact add_right_cancel b (a + k) t hk
  use k
  assumption

example (a : ℕ) (h : a + 1 ≤ 2) : a ≤ 1 := by
  rw [← succ_eq_add_one] at h
  rw [succ_eq_add_one] at h
  apply le_cancel a 1 1
  match h with
  |⟨k, e⟩ =>
  use k
  rw [two_eq_succ_one, succ_eq_add_one] at e
  assumption

lemma le_two (a : ℕ) (h : a ≤ 2) : a = 0 ∨ a = 1 ∨ a = 2 := by
  cases a with a
  · left; rfl
  · rw [succ_eq_add_one] at *
    rw [two_eq_succ_one, succ_eq_add_one] at h
    have := le_cancel a 1 1 h
    cases (le_one a this) with h1 h2
    · right; left
      rw [h1, zero_add]
      rfl
    · right; right
      rw [h2]
      rw [two_eq_succ_one, succ_eq_add_one]
      rfl

Statement prime_two :
  Prime 2 := by
  unfold Prime
  constructor
  use 0
  rw [add_zero]
  rfl
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
