import Game.Levels.Division.Level_5
import Game.Levels.AdvMultiplication.all_levels

World "Division"
Level 6
Title "dvd_add_right"

LemmaTab "∣"

namespace MyNat

Introduction
"
 We will prove that if d ∣ a + b, and d ∣ a, then we know that d ∣ b.
"

LemmaDoc MyNat.dvd_add_right as "dvd_add_right" in "∣" "
`div_add_right d a b` is a proof that `d ∣ a + b ∧ d ∣ a → d ∣ b`.
"

Statement dvd_add_right
    (d a b : ℕ) (hab : d ∣ a + b) (ha : d ∣ a) : d ∣ b := by
  rcases ha with ⟨c, rfl⟩
  rcases hab with ⟨e, he⟩
  cases d with d
  · use 0
    rw [zero_mul] at *
    rw[zero_mul] at he
    rw [zero_add] at he
    exact he
  · have : 1 ≤ succ d := by sorry
    sorry


example (a b c d : ℕ) (h : a * c + b = a * d) : a ∣ b := by
  sorry


--    obtain ⟨n, rfl⟩ := Nat.le.dest (Nat. le_of_mul_le_mul_left (Nat. le.intro hm) this) use n
--    rw [Nat. mul_add] at hm exact Nat. add_left_cancel hm
