import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual

World "LessThan"
Level 3
Title "The `tfae` tactic"

namespace MyNat

/--
`lt_iff_not_le a b` is a proof of `a < b ↔ ¬(b  ≤ x)`.

The reason for the name is that this lemma is "reflexivity of $\le$"
-/
TheoremDoc MyNat.lt_tfae as "lt_tfae" in "<"

/-- If $a\ b$ are natural numbers the a < b ↔ ¬(b ≤ a) ↔ a.succ ≤ b ↔ ∃ n : MyNat, a + n.succ = b
-/
Statement lt_tfae (a b: ℕ) :
[a < b, --old 1
a.succ ≤ b, --old 2
∃ n : MyNat, b = a.succ + n, --old 3
∃ n : MyNat, b = (a+n).succ, --old 4
∃ n : MyNat, b = a + n.succ, --old 5
∀ n : MyNat, a ≠ b + n , --old 6
 ¬(b ≤ a), --old 7
a ≤ b ∧ ¬(b ≤ a),  --old 8
].TFAE := by
  tfae_have 1 → 2
  · intro ⟨⟨n,h0⟩,h1⟩
    cases n with l
    · exfalso
      rw [add_zero] at h0
      exact h1 h0.symm
    · use l
      rw [h0,add_succ,succ_add]
      rfl
  tfae_have 2 → 3
  · exact id
  tfae_have 3 → 4
  · simp_rw [succ_add]
    exact id
  tfae_have 4 → 5
  · simp_rw [←add_succ]
    exact id
  tfae_have 5 → 6
  · intro ⟨n,hn⟩ m h0
    rw [h0,add_assoc,add_succ] at hn
    have h1 : succ (m + n) = 0 :=
      (add_right_eq_self b (succ (m + n)) ) hn.symm
    have h2 := succ_ne_zero (m + n)
    exact h2 h1
  tfae_have 6 → 7
  · intro h0
    rw [←not_exists] at h0
    exact h0
  tfae_have 7 → 8
  · intro h0
    apply And.intro
    exact Or.resolve_right (le_total a b) h0
    exact h0
  tfae_have 8 → 1
  · intro ⟨h0,h1⟩
    apply And.intro h0
    intro h2
    rw [h2] at h1
    exact h1 (le_refl b)
  tfae_finish


TheoremTab "<"
