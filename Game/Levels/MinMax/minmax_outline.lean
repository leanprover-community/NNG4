import Game.MyNat.LT
import Game.Levels.LessThan
import Mathlib.Order.Lattice

namespace MyNat

theorem T0 (a b : ℕ) : ¬( a = a + succ b) := by
  intro h0
  have h1 := add_right_eq_self a (succ b) h0.symm
  have h2 := succ_ne_zero b
  exact h2 h1

theorem lt_iff_le_not_le (a b : ℕ) : a < b ↔ a ≤ b ∧ ¬(b ≤ a) := by  
  apply Iff.intro
  rintro ⟨n,hn⟩
  apply And.intro
  use succ n
  rw [hn,add_succ,succ_add]
  rfl
  rintro ⟨m,hm⟩
  rw [hn] at hm
  rw [add_assoc,succ_add,←add_succ] at hm
  have h1 := T0 a (n + m)
  exact h1 hm

  rintro ⟨⟨n,hn⟩,h0⟩
  rw [hn] at h0 ⊢
  cases n with l
  exfalso
  rw [add_zero] at hn h0
  apply h0
  exact le_refl a
  use l
  rw [add_succ,succ_add]
  rfl

def min (a b : ℕ) := ite (a ≤ b) a b
def max (a b : ℕ) := ite (b ≤ a) a b


--protected 
theorem my_min_le_min(a b : ℕ) : min a b ≤ min b a := by
  rcases (le_total a b) with ⟨n,hnab⟩ | ⟨n,hnab⟩
  cases n with nl
  rw [add_zero] at hnab
  rw [hnab]
  use 0
  rw [add_zero]
  rfl
  unfold min
  rw [if_pos,if_neg]
  exact le_refl a
  rintro ⟨m,hmab⟩
  rw [hnab,add_assoc,succ_add] at hmab
  exact T0 a (nl + m) hmab
  use succ nl
  exact hnab
  cases n with ln
  rw [hnab,add_zero]
  exact le_refl (min b b)
  unfold min
  rw [if_neg,if_pos]
  exact le_refl b
  use (succ ln)
  exact hnab
  rintro ⟨m,hmab⟩
  rw [hnab] at hmab
  rw [add_assoc,succ_add] at hmab
  exact T0 b (ln + m) hmab


theorem min_comm (a b : ℕ) : min a b = min b a :=
  le_antisymm (min a b) (min b a) (my_min_le_min a b) (my_min_le_min b a)


instance : Preorder ℕ := {
le_refl := MyNat.le_refl
le_trans := MyNat.le_trans
lt_iff_le_not_le := MyNat.lt_iff_le_not_le
}

instance : PartialOrder ℕ := {
le_antisymm := MyNat.le_antisymm
}

instance : SemilatticeInf ℕ := {
inf := MyNat.min
inf_le_left := by
  intro a b
  dsimp
  rcases (le_total a b) with (h1 | h1)
  unfold min
  use 0
  rw [add_zero]
  rw [if_pos h1]
  rfl
  unfold min
  rcases h1 with ⟨k,hk⟩
  cases k with l
  rw [if_pos]
  exact le_refl a
  use 0
  rw [add_zero] at hk ⊢
  rw [hk]
  rfl
  rw [if_neg]
  use (succ l)
  exact hk
  rintro ⟨z,hz⟩
  rw [hk] at hz
  rw [add_assoc] at hz
  rw [succ_add] at hz
  exact T0 b (l + z) hz


inf_le_right := by
  intro a b
  dsimp
  rcases (le_total a b) with (⟨n,hn⟩ | ⟨n,hn⟩)
  unfold min
  rw [if_pos]
  use n
  exact hn
  use n
  exact hn
  unfold min
  cases n with l
  rw [if_pos]
  use 0
  rw [add_zero] at hn ⊢
  rw [hn]
  rfl
  use 0
  rw [add_zero] at hn ⊢
  rw [hn]
  rfl
  rw [if_neg]
  use 0
  rw [add_zero]
  rfl
  rintro ⟨k,hk⟩
  rw [hn] at hk
  rw [add_assoc] at hk
  rw [succ_add] at hk
  have h1 := add_right_eq_self b (succ (l + k)) hk.symm
  have h2 := succ_ne_zero (l + k)
  exact h2 h1

le_inf := by
  rintro a b c ⟨n,hnab⟩ ⟨m,hmbc⟩
  dsimp
  rw [hnab,hmbc]
  rcases (le_total n m) with (⟨ρ,hρ⟩ |⟨ρ,hρ ⟩)
  rw [hρ]
  unfold min
  rw [if_pos]
  use n
  rfl
  use ρ
  rw [add_assoc]
  rfl
  rw [hρ]
  unfold min
  cases m with lm
  cases ρ with lρ
  rw [add_zero,add_zero]
  rw [if_pos]
  use 0
  rw [add_zero]
  rfl
  use 0
  rw [add_zero]
  rfl
  rw [if_neg]
  use 0
  rfl
  rintro ⟨θ,hθ⟩
  rw [add_zero,zero_add] at hθ
  rw [add_assoc] at hθ
  have h1 := add_right_eq_self a (succ lρ + θ) hθ.symm
  rw [succ_add] at h1
  have h2 := succ_ne_zero (lρ + θ)
  exact h2 h1
  cases ρ with lρ
  rw [if_pos]
  use (succ lm)
  rw [add_zero]
  rfl
  use 0
  rw [add_zero,add_zero]
  rfl
  rw [if_neg]
  use (succ lm)
  rfl
  rintro ⟨Γ,hΓ⟩
  rw [add_succ,add_succ,add_succ,succ_add] at hΓ
  have h2 := succ_inj (a +lm) (a + (succ lm + lρ) + Γ) hΓ
  rw [add_assoc] at h2
  have h3 := add_left_cancel lm (succ lm + lρ +Γ) a h2
  rw [add_assoc] at h3
  rw [succ_add,←add_succ] at h3
  have h4 := add_right_eq_self lm (succ (lρ + Γ)) h3.symm
  have h5 := succ_ne_zero (lρ + Γ)
  exact h5 h4
}

instance : SemilatticeSup ℕ := {
sup := MyNat.max
le_sup_left := by
}
