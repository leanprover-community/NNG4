import Game.Levels.LessThan.A_L17_pow_le


World "LessThan"
Level 18
Title "TITLE"

TheoremTab "<"  --not sure

namespace MyNat

/-- NEED help on this -/
TheoremDoc MyNat.strong_induction as "strong_induction" in "<" -- not sure


Introduction "As an exercise, try to do this on paper before doing it on the computer.
The idea of the proof isn't esoteric, but it is easy to convince yourself that an invalid
proof your wrote is actually valid.  You will need to use mathematical induction."

Statement strong_induction (P : ℕ → Prop) --level 18
    (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n) : ∀ z : ℕ, P z := by
  have h1 : ∀ θ : ℕ, ∀ y : ℕ, y < θ → P y := by
    intro θ
    induction θ with k hk
    intro y hy
    exfalso
    exact ((not_lt_zero y) hy)
    intro y hy
    rcases (lt_succ_iff_le y k).mp hy with ⟨δ,hδ⟩
    cases δ with l
    rw [add_zero] at hδ
    rw [←hδ]
    exact h0 k (hk)
    apply hk
    use l
    rw [hδ, add_succ,succ_add]
    rfl
  intro z
  exact h1 (succ z) z (lt_succ_self z)

Conclusion "CONCLUSION"
