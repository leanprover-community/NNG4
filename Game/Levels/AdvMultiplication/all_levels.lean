import Game.Levels.Multiplication
import Game.Levels.LessOrEqual
import Game.MyNat.Division

namespace MyNat

-- should we be using `succ` any more????
lemma eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  cases a with d
  contradiction
  use d
  -- WTF????? **TODO** `use` shouldn't try `rfl`

lemma mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  apply eq_succ_of_ne_zero at ha
  apply eq_succ_of_ne_zero at hb
  cases ha with c hc
  cases hb with d hd
  rw [hc, hd]
  rw [mul_succ, add_succ]
  symm
  apply zero_ne_succ

lemma mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have hab := mul_ne_zero a b
  tauto

lemma mul_right_ne_zero (a b : ℕ) (h : a * b ≠ 0) : a ≠ 0 := by
  intro h1
  apply h
  rw [h1]
  rw [zero_mul]
  rfl

lemma mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  rw [mul_comm] at h
  exact mul_right_ne_zero b a h

lemma one_le_of_zero_ne (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  cases a with n
  · contradiction
  · use n
    rw [succ_eq_add_one]
    rw [add_comm]
    rfl

lemma mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  cases h with d hd
  use d * t
  rw [hd, add_mul]
  rfl

lemma le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  -- do I need `have`?
  apply mul_left_ne_zero at h
  apply one_le_of_zero_ne at h
  apply mul_le_mul_right 1 b a at h
  rw [one_mul, mul_comm] at h
  exact h

lemma le_one (a : ℕ) (ha : a ≤ 1) : a = 0 ∨ a = 1 := by
  cases a with b
  · left
    rfl
  · cases b with c
    · right
      rw [one_eq_succ_zero]
      rfl
    · cases ha with x hx
      rw [succ_add, succ_add] at hx
      rw [one_eq_succ_zero] at hx
      apply succ_inj at hx
      apply zero_ne_succ at hx
      contradiction

lemma eq_one_of_mul_right_eq_one (c d : ℕ) (h : c * d = 1) : c = 1 := by
  have foo : c ≤ 1 := by
    rw [← h]
    apply le_mul_right
    rw [h]
    symm
    apply zero_ne_succ
  apply le_one at foo
  cases foo with h0 h1
  · rw [h0, zero_mul] at h
    apply zero_ne_succ at h
    contradiction
  exact h1

lemma mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction b with d hd generalizing c -- this is what trips everyone up
  · rw [mul_zero] at h
    symm at h
    sorry -- this is NNG3 adv mult levels 1 to 3
  · cases c with c
    · rw [mul_succ, mul_zero] at h
      apply eq_zero_of_add_left_eq_zero at h
      contradiction
    · rw [mul_succ, mul_succ] at h
      apply add_right_cancel at h
      have foo : d = c := by
        apply hd
        exact h
      rw [foo]
      rfl

lemma self_eq_mul_left (a b : ℕ) (h : b = a * b) (hb : b ≠ 0) : a = 1 := by
  rw [mul_comm] at h
  nth_rewrite 1 [← mul_one b] at h
  apply mul_left_cancel at h
  rw [h]
  rfl
  exact hb

lemma self_eq_mul_right (a b : ℕ) (h : b = b * a) (hb : b ≠ 0) : a = 1 := by
  rw [mul_comm] at h
  exact self_eq_mul_left _ _ h hb


-- Extra for Prime World

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
