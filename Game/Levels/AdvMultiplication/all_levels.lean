import Game.Levels.AdvMultiplication.L06mul_right_eq_one

namespace MyNat

-- -- good level 1; used in the important `le_mul_right`
-- lemma mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
--   cases h with d hd
--   use d * t
--   rw [hd, add_mul]
--   rfl

-- -- used in `le_mul_right`
-- lemma mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
--   contrapose! h
--   have h1 : b = 0 → a * b = 0
--   · intro h2
--     rw [h2, mul_zero]
--     rfl
--   tauto

-- -- `le_mul_right` is used in `if a ∣ x and x ≠ 0 then a ≤ x`, a key fact
-- -- for proving 2 is prime! It's also used in cd=1=>c=1, which Archie needs.
-- lemma le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
--   apply mul_left_ne_zero at h
--   apply one_le_of_zero_ne at h
--   apply mul_le_mul_right 1 b a at h
--   rw [one_mul, mul_comm] at h
--   exact h

-- -- needed, with le_mul_right, to prove cd=1=>c=1
-- lemma le_one (a : ℕ) (ha : a ≤ 1) : a = 0 ∨ a = 1 := by
--   cases a with b
--   · left
--     rfl
--   · cases b with c
--     · right
--       rw [one_eq_succ_zero]
--       rfl
--     · cases ha with x hx
--       rw [succ_add, succ_add] at hx
--       rw [one_eq_succ_zero] at hx
--       apply succ_inj at hx
--       apply zero_ne_succ at hx
--       tauto

-- -- Archie needs this
-- lemma mul_right_eq_one (c d : ℕ) (h : c * d = 1) : c = 1 := by
--   have foo : c ≤ 1 := by
--     rw [← h]
--     apply le_mul_right
--     rw [h]
--     symm
--     apply zero_ne_succ
--   apply le_one at foo
--   cases foo with h0 h1
--   · rw [h0, zero_mul] at h
--     apply zero_ne_succ at h
--     tauto
--   exact h1

-- -- used in `mul_ne_zero`, which is used in `mul_eq_zero`, which is used in `mul_left_cancel`
-- lemma eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
--   cases a with d
--   tauto
--   use d
--   rfl

-- used in `mul_eq_zero`, which is used in `mul_left_cancel`
lemma mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  apply eq_succ_of_ne_zero at ha
  apply eq_succ_of_ne_zero at hb
  cases ha with c hc
  cases hb with d hd
  rw [hc, hd]
  rw [mul_succ, add_succ]
  symm
  apply zero_ne_succ

-- used in `mul_left_cancel`
lemma mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have foo := mul_ne_zero a b
  tauto


-- very natural goal; challenging. Also used in `mul_left_eq_self`, which Archie needs.
lemma mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction b with d hd generalizing c -- this is what trips everyone up
  · rw [mul_zero] at h
    symm at h
    apply mul_eq_zero at h
    cases h with h1 h2
    · tauto
    · rw [h2]
      rfl
  · cases c with c
    · rw [mul_succ, mul_zero] at h
      apply add_left_eq_zero at h
      tauto
    · rw [mul_succ, mul_succ] at h
      apply add_right_cancel at h
      rw [hd c]
      rfl
      exact h

-- Archie needs this
lemma mul_left_eq_self (a b : ℕ) (h : b = a * b) (hb : b ≠ 0) : a = 1 := by
  rw [mul_comm] at h
  nth_rewrite 1 [← mul_one b] at h
  apply mul_left_cancel at h
  rw [h]
  rfl
  exact hb
