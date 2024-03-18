import Game.MyNat.Addition

namespace MyNat

-- TODO: Is there a better way to do this instead of reproving these
-- basic theorems?

theorem add_assocₓ (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    rw [zero_eq_0, add_zero, add_zero]
  | succ n hn =>
    rw [add_succ, add_succ, add_succ, hn]

theorem succ_addₓ : succ b + a = succ (b + a) := by
      induction a with
      | zero =>
        rw [zero_eq_0, add_zero, add_zero]
      | succ a ha =>
        rw [add_succ, add_succ, ha]

theorem add_commₓ (a b : ℕ) : a + b = b + a := by
  induction b with
  | zero =>
    have zero_add : 0 + a = a := by
      induction a with
      | zero => rw [zero_eq_0, add_zero]
      | succ a ha =>
        rw [add_succ, ha]
    rw [zero_eq_0, add_zero, zero_add]
  | succ b hb =>
    rw [add_succ, succ_addₓ, hb]

theorem add_left_commₓ (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assocₓ, add_commₓ a b, add_assocₓ]

macro "simp_add" : tactic => `(tactic|(
  simp only [add_assocₓ, add_left_commₓ, add_commₓ]))
