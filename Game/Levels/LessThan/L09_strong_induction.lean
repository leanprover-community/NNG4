import Game.Levels.LessThan.L08_lt_trans

World "LessThan"
Level 9
Title "strong induction"

TheoremTab "<"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.strong_induction as "strong_induction" in "<"

Introduction ""

theorem not_lt_zero (a : ℕ) : ¬(a < 0) := by
  intro ⟨⟨n,h0⟩,h1⟩
  apply h1
  exact add_right_eq_zero a n (h0.symm)

theorem lt_succ_iff (a k : ℕ)  : a < succ k ↔ a < k ∨ a = k := by
  apply Iff.intro
  intro h0
  rw [lt_iff_exists_add_succ] at h0
  rcases h0 with ⟨c,hc⟩
  rw [add_succ] at hc
  have hd := succ_inj k (a + c) hc
  rw [hd]
  clear hc
  cases c with l
  apply Or.inr
  rw [add_zero]
  rfl
  apply Or.inl
  rw [lt_iff_exists_add_succ]
  use l
  rfl
  rintro (h0|h0)
  rw [lt_iff_exists_add_succ] at *
  rcases h0 with ⟨c,hc⟩
  use (succ c)
  rw [hc,add_succ,add_succ,add_succ]
  rfl
  rw [lt_iff_exists_add_succ]
  use 0
  rw [add_succ,h0,add_zero]
  rfl


Statement strong_induction_1 {P : ℕ → Prop} (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P (n)) : ∀ z : ℕ,  P z := by
  have h1 : ∀ z : ℕ, ∀ y : ℕ, y < z → P y := by
    intro z
    induction z with k hk
    intro y hy
    exfalso
    have h1 := not_lt_zero y
    exact h1 hy
    intro y hy
    have h1 : y < k ∨ y = k := by
      rw [lt_succ_iff] at hy
      exact hy
    rcases h1 with (h1 | h1)
    exact hk y h1
    specialize h0 y
    rw [←h1] at hk
    apply h0
    exact hk
  intro y
  specialize h1 (succ y) y
  apply h1
  rw [lt_iff_exists_add_succ]
  use 0
  rw [add_succ,add_zero]
  rfl


Conclusion "
Here's my proof:
```
something
```
"
