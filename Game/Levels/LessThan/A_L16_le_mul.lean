import Game.Levels.LessThan.A_L15_mul_lt_mul_of_pos_left

World "LessThan"
Level 16
Title "le_mul"

TheoremTab "≤"  --double check that this is correct.

namespace MyNat

/-- `le_mul a b c d` is a proof that `a ≤ b → c ≤ d → a * c ≤ b * d` -/
TheoremDoc MyNat.le_mul as "le_mul" in "≤"

Introduction "In this level we show that we can multiply two
`≤`-relations term-by-term and retain a valid `≤`-relation."

/--
We can multiply two `≤`-relations term-by-term and retain a valid `≤`-relation.
-/
Statement le_mul (a b c d : ℕ ) : a ≤ b → c ≤ d → a * c ≤ b * d := by
  Hint"What number is `b * d - a * c`?"
  intro ⟨n,hab⟩ ⟨m,hcd⟩
  rw [hab,hcd,add_mul,mul_add,mul_add]
  use (a * m + (n * c + n * m))
  rw [add_assoc (a * c) ]
  rfl

theorem add_eq_one (a b : ℕ) : a + b = 1 → a = 1 ∨ b = 1 := by
  intro h0
  induction b with k hk
  rw [add_zero] at h0
  left
  exact h0
  cases a with l
  right
  rw [zero_add] at h0
  exact h0
  exfalso
  rw [one_eq_succ_zero,succ_add] at h0
  have h1 := succ_inj 0 (l + succ k) h0.symm
  rw [add_succ] at h1
  have h2 := zero_ne_succ (l + k)
  exact h2 h1
  


theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  by_contra h0
  induction y with k hk
  rw [mul_zero] at h
  apply zero_ne_one h
  rw [mul_succ] at h
  have h1 := add_eq_one (x * k) x h
  cases h1 with h1 h1
  exact hk h1
  exact h0 h1

theorem T0 (x y : ℕ) (h : x * y = 2) : x = 2 ∨ y = 2 := by
  cases x with lx
  exfalso
  rw [zero_mul] at h
  rw [two_eq_succ_one] at h
  exact zero_ne_succ 1 h
  cases lx with llx
  rw [←one_eq_succ_zero] at h
  rw [one_mul] at h
  right
  exact h
  cases y with m
  exfalso
  rw [mul_zero] at h
  rw [two_eq_succ_one] at h
  exact zero_ne_succ 1 h
  left
  cases llx
  rw [two_eq_succ_one,one_eq_succ_zero]
  rfl
  exfalso
  rw [two_eq_succ_one,one_eq_succ_zero,succ_mul,add_succ] at h
  have h1 := succ_inj (succ (succ a) * succ m + m) (succ 0) h
  rw [mul_succ,add_succ,succ_add] at h1
  have h2 := succ_inj (succ (succ a) * m + succ a + m) 0 h1
  have h3 := add_left_eq_zero _ m h2
  rw [h3,add_zero,mul_zero,zero_add] at h2
  exact succ_ne_zero a h2
  

theorem T3 (x y : ℕ) (h : x * y = 3) : x = 3 ∨ y = 3 := by
  cases x with lx
  exfalso
  rw [zero_mul] at h
  have h1 : (0:ℕ)  ≠(3:ℕ)  := ne_of_beq_false _root_.rfl
  exact h1 h
  cases lx with llx
  right
  rw [←one_eq_succ_zero] at h
  rw [one_mul] at h
  exact h
  cases y with my
  rw [mul_zero] at h
  exfalso
  have h1 : (0:ℕ)  ≠(3:ℕ)  := ne_of_beq_false _root_.rfl
  exact h1 h
  rw [succ_mul,add_succ] at h
  rw [three_eq_succ_two] at h
  have h1 := succ_inj (succ llx * succ my + my) 2 h
  rw [two_eq_succ_one] at h1
  rw [mul_succ] at h1
  rw [add_assoc] at h1
  rw [succ_add] at h1
  rw [add_succ] at h1
  have h2 := succ_inj (succ llx * my + (llx + my)) 1 h1
  rw [succ_mul] at h2
  have h3 := add_eq_one _ _ h2
  cases h3 with h3 h3
  have h4 := add_eq_one _ _ h3
  cases h4 with h4 h4
  have h5 := mul_right_eq_one llx my h4
  rw [mul_comm] at h4  
  left
  rw [h5,three_eq_succ_two,two_eq_succ_one]
  rfl
  exfalso
  rw [h4,mul_one] at h3
  have h5 := add_left_eq_self llx 1 h3
  rw [h4,h5,zero_mul,zero_add] at h2
  have h6 := add_left_eq_self 1 1 h2
  exact one_ne_zero h6
  have h4 := add_eq_one llx my h3
  cases h4 with h4 h4
  left
  rw [h4,three_eq_succ_two,two_eq_succ_one]
  rfl
  rw [h4,mul_one,←succ_eq_add_one,add_succ,one_eq_succ_zero] at h2
  have h5 := succ_inj (succ llx + llx) 0 h2
  rw [succ_add] at h5
  exfalso
  have h6 := succ_ne_zero (llx + llx)
  exact h6 h5

