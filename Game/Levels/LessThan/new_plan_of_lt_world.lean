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

--level 3
theorem succ_succ_eq_succ_succ_iff (a b : ℕ) :
  succ (succ a) = succ (succ b) ↔ a = b := by
  rw [succ_eq_succ_iff]
  rw [succ_eq_succ_iff]
  rfl

--level 3.5
theorem lt_self_succ (a : ℕ) : a < succ a := by
  use 0
  rw [add_zero]
  rfl

--level 4
theorem not_lt_zero (a : ℕ) : ¬(a < 0) := by
  intro h0
  cases h0 with θ h0
  rw [succ_add] at h0
  have h1 := zero_ne_succ (a + θ)
  exact h1 h0


--level 5
theorem lt_iff (a b : ℕ) :
  a < b ↔ ¬(b ≤ a) := by
  constructor
  intro h0 h1
  cases h0 with θ h0
  cases h1 with φ h1
  rw [h0,succ_add,succ_add,add_assoc,←add_succ] at h1
  have h2 := add_right_eq_self a (succ (θ + φ)) h1.symm
  have h3 := succ_ne_zero (θ + φ)
  exact h3 h2
  intro h0
  cases le_total b a with h
  exfalso
  exact h0 h
  cases h with θ h
  cases θ with l
  exfalso
  rw [add_zero] at h
  rw [h] at h0
  have h2 := le_refl a
  exact h0 h2
  use l
  rw [succ_add,←add_succ]
  exact h

--level 6
theorem lt_iff' (a b : ℕ) :
  a < b ↔ (a ≤ b) ∧ ¬(b ≤ a) := by
  rw [lt_iff]
  constructor
  intro h0
  constructor
  cases le_total a b with h
  exact h
  exfalso
  exact h0 h
  exact h0
  intro h0
  cases h0 with h0l h0r
  exact h0r

--level 7
theorem lt_succ_iff_le (m n : ℕ) : m < succ n ↔ m ≤ n := by -- Level 09
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
theorem not_lt_and_lt_succ (m n : ℕ) : ¬( (n < m) ∧ (m < succ n)) := by
  rintro ⟨h0,h1⟩
  rw [lt_succ_iff_le] at h1
  rw [lt_iff] at h0
  exact h0 h1






-- --symm notation?
-- theorem add_right_succ_ne_self (a b : ℕ) : ¬(a = a + succ b) := by
--   intro h0
--   have h1  := add_right_eq_self a (succ b) h0.symm
--   have h2 := succ_ne_zero b
--   exact h2 h1


-- --rintro
-- theorem lt_irrefl (a : ℕ) : ¬(a < a) := by --level 01
--   rintro ⟨n,hn⟩
--   rw [succ_add,←add_succ] at hn
--   have h1 := add_right_succ_ne_self a n
--   exact h1 hn

-- --contrapose tactic
-- theorem ne_of_lt (a b : ℕ) : a < b → a ≠ b := by --level 02
--   contrapose!
--   intro h0
--   rw [h0]
--   exact lt_irrefl b

-- theorem not_lt_zero (a : ℕ) : ¬(a < 0) := by --level 03
--   intro ⟨n,hn⟩
--   rw [succ_add] at hn
--   have h1 := succ_ne_zero (a + n)
--   exact h1 hn.symm

-- --Exists.intro? --never used
-- theorem lt_of_lt_of_le (a b c : ℕ) : a < b → b ≤ c → a < c := by --level 04
--   rintro ⟨n,hnab⟩ ⟨m,hmbc⟩
--   use (n + m)
--   rw [hmbc,hnab,add_assoc]
--   rfl

-- --never used
-- --repeat?
-- theorem lt_of_le_of_lt (a b c : ℕ) : a ≤ b → b < c → a < c := by --level 05
--   intro ⟨n,hnab⟩ ⟨m,hmbc⟩
--   use (n + m)
--   rw [hmbc,hnab]
--   repeat rw [succ_add]
--   rw [add_assoc]
--   rfl

-- theorem lt_trans (a b c : ℕ) : a < b → b < c → a < c := by  --level 06
--   intro ⟨n,hnab⟩ ⟨m,hmbc⟩
--   use ((n + m).succ)
--   rw [hmbc,hnab]
--   repeat rw [succ_add]
--   rw [add_succ,add_assoc]
--   rfl

-- theorem lt_succ_self (a : ℕ) : a < a.succ := by --level 07
--   use 0
--   have h1 := add_zero (succ a)
--   exact h1.symm

-- --question for Kevin, this is called succ_le_succ in mathlib.  You had it originally as succ_le_succ
-- --there is theorem in LessOrEqual world, that is named succ_le_succ but it is only the forward implication
-- --I propose that we change that to be an iff, but I will leave it alone for now.

-- theorem succ_le_succ_iff(m n : ℕ) : succ m ≤ succ n ↔ m ≤ n := by --level 08
--   apply Iff.intro (succ_le_succ m n)
--   intro ⟨a,ha⟩
--   rw [ha]
--   use a
--   rw [succ_add]
--   rfl

-- -- Iff.intro
-- theorem lt_succ_iff_le (m n : ℕ) : m < succ n ↔ m ≤ n := by -- Level 09
--   apply Iff.intro
--   intro ⟨k,hk⟩
--   rw [succ_add] at hk
--   have hk1 := succ_inj n (m + k) hk
--   exact Exists.intro k hk1
--   intro ⟨k,hk⟩
--   use k
--   rw [hk]
--   rw [succ_add]
--   rfl

-- theorem lt_of_add_lt_add_left (a b c : ℕ) : a + b < a + c → b < c := by --level 10
--   intro ⟨n,hn⟩
--   rw [succ_add,add_assoc,←add_succ,←add_succ] at hn
--   have h1 := add_left_cancel c (b + succ n) a hn
--   use n
--   rw [h1,add_succ,succ_add]
--   rfl

-- theorem add_lt_add_right (a b : ℕ) : a < b → ∀ c : ℕ, a + c < b + c := by --level 11
--   rintro ⟨n,hn⟩
--   intro c
--   use n
--   rw [hn,add_assoc,add_comm n c]
--   repeat rw [succ_add]
--   rw [add_assoc]
--   rfl

-- --instances ordered_comm_monoid

-- --Should we add something here to show how we can use this fact?

-- --canonically_ordered_comm_monoid
-- --ordered_cancel_comm_moniod

-- theorem succ_lt_succ_iff (a b : ℕ) : succ a < succ b ↔ a < b := by --level 12
--   rw [lt_iff_succ_le,lt_iff_succ_le]
--   exact succ_le_succ_iff (succ a) b

-- theorem mul_le_mul_of_nonneg_left (a b c: ℕ) --level 13
--     : a ≤ b → 0 ≤ c → a * c ≤ b * c := by
--   intro ⟨n,hab⟩
--   intro cnneg
--   clear cnneg
--   use (c * n)
--   rw [hab,add_mul]
--   rw [mul_comm n c]
--   rfl

-- theorem mul_lt_mul_of_pos_right (a b c : ℕ) --level 14
--     : b < c → 0 < a → b * a < c * a := by
--   intro ⟨n,hbc⟩
--   intro ⟨d,ha⟩
--   rw [succ_add,zero_add] at ha
--   rw [hbc,ha]
--   rw [add_mul,succ_mul]
--   use (d + n * succ d)
--   rw [mul_succ,mul_succ,add_succ,succ_add,succ_add]
--   rw [add_assoc ((b * d) + b)]
--   rfl

-- theorem mul_lt_mul_of_pos_left (a b c : ℕ) --level 15
--     : b < c → 0 < a → a * b < a * c  := by
--   rw [mul_comm a b, mul_comm a c]
--   exact mul_lt_mul_of_pos_right a b c

-- --instance ordered semiring

-- theorem le_mul (a b c d : ℕ ) : a ≤ b → c ≤ d → a * c ≤ b * d := by --level 16
--   intro ⟨n,hab⟩ ⟨m,hcd⟩
--   rw [hab,hcd,add_mul,mul_add,mul_add]
--   use (a * m + (n * c + n * m))
--   rw [add_assoc (a * c) ]
--   rfl

-- theorem pow_le (m n a : ℕ) : m ≤ n → m ^ a ≤ n ^ a := by --level 17
--   intro hmn
--   induction a with l hl
--   rw [pow_zero,pow_zero]
--   exact le_refl 1
--   rw [pow_succ]
--   rw [pow_succ]
--   apply le_mul
--   exact hl
--   exact hmn


-- --Try to do this on paper before doing it on the computer. 
-- --strong induction
-- theorem strong_induction (P : ℕ → Prop) --level 18
--     (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n) : ∀ z : ℕ, P z := by
--   have h1 : ∀ θ : ℕ, ∀ y : ℕ, y < θ → P y := by
--     intro θ
--     induction θ with k hk
--     intro y hy
--     exact False.elim ((not_lt_zero y) hy)
--     intro y hy
--     rcases (lt_succ_iff_le y k).mp hy with ⟨δ,hδ⟩
--     cases δ with l
--     rw [add_zero] at hδ
--     rw [←hδ]
--     exact h0 k (hk)
--     specialize hk y
--     apply hk
--     use l
--     rw [hδ]
--     rw [add_succ,succ_add]
--     rfl
--   intro z
--   exact h1 (succ z) z (lt_succ_self z)

-- --should we have a level where we need to use strong induction?




end MyNat
