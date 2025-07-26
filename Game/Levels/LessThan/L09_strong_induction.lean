import Game.Levels.LessThan.L08_not_lt_and_lt_succ

World "LessThan"
Level 9
Title "Strong Induction Principle"

TheoremTab "<"  --not sure

namespace MyNat

/-- 'strong_induction P h` is a proof that `∀ z : ℕ, P z`.
-/
TheoremDoc MyNat.strong_induction as "strong_induction" in "Peano" -- not sure


Introduction "Welcome to the boss level.  Your task is to prove a
variant of basic induction called *strong induction*.  Remember that
in basic induction, you prove that a predicate `P` is true for all
natural numbers `n`.  You do this by showing `P 0`: a proof of the predicate
for `k = 0`, and then by showing that for all `k`, `P k → P (succ k)`.

The strong induction show show that that a predicate `P` is true for
all natural numbers `n`.  It does this with a weaker \"inductive
hypothesis\". For `n` the strong inductive hypotheses is a proof that
for all `m < n, P m` implies `P n`.

Your task in this level, and the boss of this world, is to use the
basic induction to prove the principle of strong induction.

As an exercise, try to do this on paper before doing it
on the computer.  The idea of the proof isn't esoteric, but it is easy
to convince yourself that an invalid proof is actually
valid."

Statement strong_induction (P : ℕ → Prop)
    (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n) : ∀ z : ℕ, P z := by
  intro z
  Hint "As a warm up, try to prove the statment for `z = 0`, `z = 1`,
  and `z = 2` first.  This should give you an idea that you need to
  introduce an auxillary statement.  There is a hidden hint if you are
  still stuck."
  Branch
    induction z with k hk
    have h1 := h0 0
    apply h1
    intro m hm
    have h2 : ¬(m < 0) := not_lt_zero m
    have h3 := h2 hm
    tauto


    Hint "You are likely in a dead end.  The inductive hypothesis gives
    you `P {k}`, but to use `{h0}`, you need `∀ m < succ {k}, P m`, something
    you don't have.  You may want to restart from the beginning."
    sorry

  Hint (hidden := true) "Finish the following statement
  `have h1 : ∀ a: ℕ, ∀ y : ℕ, y < a → P y := by`"

  have h1 : ∀ θ : ℕ, ∀ y : ℕ, y < θ → P y := by
    intro θ
    induction θ with k hk
    intro y hy
    have h1 := not_lt_zero y
    have h2 := h1 hy
    tauto
    intro y hy
    have h3 := (lt_succ_iff_le y k).mp hy
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


Conclusion "Congratulations.  You have finished the `<` level.  Click
\"Leave World\" to go back to the overworld."

