import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual
import Game.Levels.AdvMultiplication
import Game.Levels.Power

namespace MyNat



theorem lt_irrefl (a : ℕ) : ¬(a < a) := by
  intro h0
  rw [lt_iff_succ_le] at h0
  rcases h0 with ⟨n,hn⟩
  rw [succ_add,←add_succ] at hn
--  have h0 : succ n = 0 := add_right_eq_self
  have h1 := add_right_eq_self a (succ n) hn.symm
  have h2 := succ_ne_zero n
  exact h2 h1

theorem ne_of_lt (a b : ℕ) : a < b → a ≠ b := by
  contrapose!
  intro h0
  rw [h0]
  exact lt_irrefl b

theorem not_lt_zero (a : ℕ) : ¬(a < 0) := by
  intro ⟨n,hn⟩
  rw [succ_add] at hn
  have h1 := succ_ne_zero (a + n)
  exact h1 hn.symm

theorem lt_of_lt_of_le (a b c : ℕ) : a < b → b ≤ c → a < c := by
  intro ⟨n,hnab⟩ ⟨m,hmbc⟩
  use (n + m)
  rw [hmbc,hnab,add_assoc]
  rfl

theorem lt_of_le_of_lt (a b c : ℕ) : a ≤ b → b < c → a < c := by
  intro ⟨n,hnab⟩ ⟨m,hmbc⟩
  use (n + m)
  rw [hmbc,hnab,succ_add,succ_add,add_assoc]
  rfl

theorem lt_trans (a b c : ℕ) : a < b → b < c → a < c := by
  intro ⟨n,hnab⟩ ⟨m,hmbc⟩
  use ((n + m).succ)
  rw [hmbc,hnab]
  rw [succ_add,succ_add,succ_add,succ_add,add_succ,add_assoc]
  rfl

theorem lt_succ_self (a : ℕ) : a < a.succ := by
  use 0
  rw [add_zero]
  rfl

theorem succ_le_succ_iff (m n : ℕ) : succ m ≤ succ n ↔ m ≤ n := by
  apply Iff.intro
  intro ⟨a,ha⟩
  use a
  rw [succ_add] at ha
  exact succ_inj n (m + a) ha
  intro ⟨a,ha⟩
  rw [ha]
  use a
  rw [succ_add]
  rfl

theorem lt_succ_iff_le (a b : ℕ) : m < succ n ↔ m ≤ n := by
  apply Iff.intro
  intro ⟨k,hk⟩
  rw [succ_add] at hk
  have hk1 := succ_inj n (m + k) hk
  exact Exists.intro k hk1
  intro ⟨k,hk⟩
  rw [hk]
  use k
  rw [succ_add]
  rfl


theorem lt_of_add_lt_add_left (a b c : ℕ) : a + b < a + c → b < c := by
  intro ⟨n,hn⟩
  rw [succ_add,add_assoc,←add_succ,←add_succ] at hn
  have h1 := add_left_cancel c (b + succ n) a hn
  use n
  rw [h1]
  rw [add_succ,succ_add]
  rfl

theorem add_lt_add_right (a b : ℕ) : a < b → ∀ c : ℕ, a + c < b + c := by
  rintro ⟨n,hn⟩
  intro c
  use n
  rw [hn]
  rw [add_assoc,add_comm n c]
  rw [succ_add,succ_add,add_assoc]
  rfl

--succ_lt_succ_iff

--instances : something

theorem succ_lt_succ_iff (a b : ℕ) : succ a < succ b ↔ a < b := by
  rw [lt_iff_succ_le,lt_iff_succ_le]
  exact succ_le_succ_iff (succ a) b

theorem mul_le_mul_of_nonneg_left (a b c: ℕ)
    : a ≤ b → 0 ≤ c → a * c ≤ b * c := by
  intro ⟨n,hab⟩
  intro cnneg
  clear cnneg
  use (c * n)
  rw [hab,add_mul]
  rw [mul_comm n c]
  rfl

theorem mul_lt_mul_of_pos_right (a b c : ℕ)
    : a < b → 0 < c → c * a < c * b := by
  intro ⟨n,hab⟩
  intro ⟨d,hc⟩
  rw [succ_add,zero_add] at hc
  rw [hab,hc]
  rw [mul_add,mul_succ]
  use (d + succ d * n)
  rw [succ_mul,succ_mul,add_succ,succ_add,succ_add]
  repeat rw [add_assoc]
  rfl

--ordered semiring instance

theorem le_mul (a b c d : ℕ ) : a ≤ b → c ≤ d → a * c ≤ b * d := by
  intro ⟨n,hab⟩ ⟨m,hcd⟩
  rw [hab,hcd,add_mul,mul_add,mul_add]
  use (a * m + (n * c + n * m))
  rw [add_assoc (a * c) ]
  rfl

theorem pow_le (m n a : ℕ) : m ≤ n → m ^ a ≤ n ^ a := by  
  intro hmn
  induction a with l hl
  rw [pow_zero,pow_zero]
  exact le_refl 1
  rw [pow_succ]
  rw [pow_succ]
  apply le_mul
  exact hl
  exact hmn


--strong induction
theorem strong_induction_aux (P : ℕ → Prop)
    (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n) : ∀ z : ℕ, P z := by
  have h1 : ∀ θ : ℕ, ∀ y : ℕ, y < θ → P y := by
    intro θ
    induction θ with k hk
    intro y hy
    exact False.elim ((not_lt_zero y) hy)
    intro y hy
    have h1 := @lt_succ_iff_le 


end MyNat
