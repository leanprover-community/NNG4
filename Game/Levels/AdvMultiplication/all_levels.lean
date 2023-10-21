import Game.Levels.Multiplication
import Game.Levels.LessOrEqual

namespace MyNat

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

-- it's not called this
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

example (c d : ℕ) (h : c * d = 1) : c = 1 := by
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

example (a b : ℕ) (h : b = a * b) (hb : b ≠ 0) : a = 1 := by
  rw [mul_comm] at h
  nth_rewrite 1 [← mul_one b] at h
  apply mul_left_cancel at h
  rw [h]
  rfl
  exact hb
