import Game.Levels.AdvAddition.L11add_right_eq_self

namespace MyNat

def le (a b : ℕ) : Prop := ∃ c, b = a + c

instance : LE MyNat := ⟨le⟩

example (x : ℕ) : 0 ≤ x := by
  use x -- **************** need `use` tactic
  rw [zero_add]
  rfl

example (x : ℕ) : x ≤ x := by
  use 0
  rw [add_zero]
  rfl

example (x : ℕ) : x ≤ succ x := by
  use 1
  rw [succ_eq_add_one]
  rfl

example (x y : Nat) : x + y = 0 → x = 0 := by exact?

-- **TODO** ask on Zulip: why is this not called eq_zero_of_add_left_eq_zero ?
#check Nat.eq_zero_of_add_eq_zero_left -- (h : n + m = 0) : m = 0

#check add_right
axiom eq_zero_of_add_eq_zero_right (x y : ℕ) (h : x + y = 0) : x = 0 -- ***************** need this

example (x : ℕ) (h : x ≤ 0) : x = 0 := by
  cases' h with n hn -- ************************ need `cases` tactic
  rw [eq_comm] at hn -- ************************ ouch, need `rw` with iffs
  apply eq_zero_of_add_eq_zero_right at hn
  assumption

example (x y z : ℕ) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hm, hn]
  use n + m
  rw [add_assoc]
  rfl

example (x y : ℕ) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hm] at hn
  rw [add_assoc] at hn
  rw [eq_comm] at hn -- ***************** more rw with iff
  apply add_right_eq_self at hn
  apply add_eq_zero at hn
  rw [hn, add_zero] at hm
  assumption

example (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  -- ******************************* need `∨`
  induction x with d hd
  left -- *********************** need `left`
  use y
  rw [zero_add]
  rfl
  cases' hd with h1 h2 -- ***************** cases on an or
  cases' h1 with n hn -- ***************** cases on a prop
  cases' n with n -- ******************* cases on a nat
  change y = d + 0 at hn
  rw [add_zero] at hn
  right -- ***************************** need `right`
  rw [hn]
  use 1
  rw [succ_eq_add_one]
  rfl
  rw [add_succ] at hn
  left
  rw [hn]
  -- succ a ≤ succ b ↔ a ≤ b would have been handy here
  rw [succ_eq_add_one, succ_eq_add_one]
  use n
  rw [add_right_comm]
  rfl
  right
  cases' h2 with n
  use n + 1
  rw [succ_eq_add_one, h]
  rw [add_assoc]
  rfl



#exit
a) 0 ≤ x;
b) x ≤ x;
c) x ≤ S(x);
d) If x ≤ 0 then x = 0.
a) x ≤ x (reflexivity);
b) If x ≤ y and y ≤ z then x ≤ z (transitivity);
c) If x ≤ y and y ≤ x then x = y (antisymmetry);
d) Either x ≤ y or y ≤ x (totality).
