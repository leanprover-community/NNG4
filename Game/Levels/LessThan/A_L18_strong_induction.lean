import Game.Levels.LessThan.A_L17_pow_le


World "LessThan"
Level 18
Title "Strong Induction Principle"

TheoremTab "<"  --not sure

namespace MyNat

/-- 'strong_induction P h` is a proof that `∀ z : ℕ, P z`.
-/
TheoremDoc MyNat.strong_induction as "strong_induction" in "<" -- not sure


Introduction "As an exercise, try to do this on paper before doing it
on the computer.  The idea of the proof isn't esoteric, but it is easy
to convince yourself that an invalid proof your wrote is actually
valid.  You will need to use mathematical induction."

Statement strong_induction (P : ℕ → Prop)
    (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n) : ∀ z : ℕ, P z := by
  intro z

  Hint "As a warm up, try to prove the statment for `z = 0`, `z = 1`,
  and `z = 2` first.  This should give you an idea that you need to
  introduce an auxillary statement.  There is a hidden hint if you are
  still stuck."

  Hint (hidden := true) "Finish the following statement
  `have h1 : ∀ a: ℕ, ∀ y : ℕ, y < a → P y := by`"

  have h1 : ∀ θ : ℕ, ∀ y : ℕ, y < θ → P y := by
    intro θ
    induction θ with k hk
    intro y hy
    have h1 := not_lt_zero y
    tauto
    intro y hy
    cases (lt_succ_iff_le y k).mp hy with δ hδ
    cases δ with l
    rw [add_zero] at hδ
    rw [←hδ]
    exact h0 k (hk)
    apply hk
    use l
    rw [hδ, add_succ,succ_add]
    rfl

  exact h1 (succ z) z (lt_succ_self z)

Conclusion "Congratulations.  You have finished the `<` level and the
natural numbers game.  For more games like this please visit URL"
