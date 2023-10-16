import Game.Levels.AdvMultiplication

World "Division"
Level 6
Title "div_add_right"

Introduction
"
 We will prove that if d ∣ a + b, and d ∣ a, then we know that d ∣ b.
"

-- example proof from `Niels` on the discord
Statement
    (d a b : ℕ) (hab : d ∣ a + b) (ha : d ∣ a) : d ∣ b := by
  rcases ha with ⟨c, rfl⟩
  rcases hab with ⟨d, hd⟩
  cases' d with d
  · have : b = 0 := by simpa using hm
    rw [this]
  · have: 1 ≤ x. succ : = Nat.le.intro (Nat.one_add x)
    obtain (n, rfl) := Nat.le.dest (Nat. le_of_mul_le_mul_left (Nat. le.intro hm) this) use n
    rw [Nat. mul_add] at hm exact Nat. add_left_cancel hm


Conclusion
"

"
