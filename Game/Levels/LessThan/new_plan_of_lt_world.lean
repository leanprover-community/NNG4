import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual
import Game.Levels.AdvMultiplication
import Game.Levels.Power

namespace MyNat


--level 1
--constuctor tactic
theorem  succ_eq_succ_iff (a b : ℕ) : succ a = succ b ↔ a = b := by
  constructor
  intro h0
  have h1 := succ_inj a b h0
  exact h1
  intro h0
  rw [h0]
  rfl

--level 2
--mainly here as practice using rw with iff statements.
theorem succ_succ_eq_succ_succ_iff (a b : ℕ) :
  succ (succ a) = succ (succ b) ↔ a = b := by
  rw [succ_eq_succ_iff]
  rw [succ_eq_succ_iff]
  rfl

--level 3
--rw tactic with iff
theorem succ_le_succ_iff (a b : ℕ) : succ a ≤ succ b ↔ a ≤ b := by
  constructor
  intro h0
  cases h0 with θ h0
  rw [succ_add] at h0
  rw [succ_eq_succ_iff] at h0
  use θ
  exact h0
  intro h0
  cases h0 with θ h0
  rw [h0]
  use θ
  rw [succ_add]
  rfl



--level 4
theorem lt_succ_self (a : ℕ) : a < succ a := by
  use 0
  rw [add_zero]
  rfl

--level 5
theorem not_lt_zero (a : ℕ) : ¬(a < 0) := by
  intro h0
  cases h0 with θ h0
  rw [succ_add] at h0
  have h1 := zero_ne_succ (a + θ)
  exact h1 h0


--level 6
--only included because then we need it to prove we have a
--partial where < and ≤ play nice.  I think if you don't have a `<`
--operater then lean defines `a < b` as `(a ≤ b) ∧ ¬(b ≤ a)`, so since
--we have a custom < we probably need the following.

--I don't have strong objections to removing it
theorem lt_iff' (a b : ℕ) :
  a < b ↔ (a ≤ b) ∧ ¬(b ≤ a) := by
  constructor
  rintro ⟨r,h0⟩
  constructor
  use (succ r)
  rw [add_succ,←succ_add]
  exact h0
  rintro ⟨r1,h1⟩
  rw [h0] at h1
  rw [add_assoc] at h1
  rw [succ_add,←add_succ] at h1
  have h2 := add_right_eq_self a (succ (r + r1)) h1.symm
  have h3 := succ_ne_zero (r + r1)
  exact h3 h2
  rintro ⟨⟨r,h0⟩,h1⟩
  rw [h0]
  cases r with l
  exfalso
  rw [add_zero] at h0
  apply h1
  use 0
  rw [add_zero,h0]
  rfl
  use l
  rw [add_succ,succ_add]
  rfl

--  instances ordered_comm_monoid
--  canonically_ordered_comm_monoid
--  ordered_cancel_comm_moniod


--level 7
--I used this in the proof of strong induction
theorem lt_succ_iff_le (m n : ℕ) : m < succ n ↔ m ≤ n := by 
  apply Iff.intro
  intro ⟨k,hk⟩
  rw [succ_add] at hk
  have hk1 := succ_inj n (m + k) hk
  exact Exists.intro k hk1
  intro ⟨k,hk⟩
  use k
  rw [hk]
  rw [succ_add]
  rfl

--level 8
--I just think this one is important.  We can get rid of it. ¬(n < m < n+1)
theorem not_lt_and_lt_succ (m n : ℕ) : ¬( (n < m) ∧ (m < succ n)) := by
  rintro ⟨h0,h1⟩
  rw [lt_succ_iff_le] at h1
  rw [lt_iff'] at h0
  rcases h0 with ⟨_h1,h01⟩
  exact h01 h1


--level 9
--Try to do this on paper before doing it on the computer. 
--strong induction
theorem strong_induction (P : ℕ → Prop) --level 9
    (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n) : ∀ z : ℕ, P z := by
  have h1 : ∀ θ : ℕ, ∀ y : ℕ, y < θ → P y := by
    intro θ
    induction θ with k hk
    intro y hy
    exact False.elim ((not_lt_zero y) hy)
    intro y hy
    rcases (lt_succ_iff_le y k).mp hy with ⟨δ,hδ⟩
    cases δ with l
    rw [add_zero] at hδ
    rw [←hδ]
    exact h0 k (hk)
    specialize hk y
    apply hk
    use l
    rw [hδ]
    rw [add_succ,succ_add]
    rfl
  intro z
  exact h1 (succ z) z (lt_succ_self z)

--End of Level



--advanced lt world would then be dedicated to showing that
--the nats are an ordered ring.  (the multiplication and addition and so on)






end MyNat
