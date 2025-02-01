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
[a < b, --old 1 --new 1
 ¬(b ≤ a), --old 2 --new 1
∃ n : MyNat, a.succ + n = b, --old 5 --new 3
∃ n : MyNat, (a+n).succ = b, --old 6 --new 4
∃ n : MyNat, a + n.succ = b, --old 4 --new 5
a.succ ≤ b, --old 3 --new 6



].TFAE := by
  tfae_have 1 → 2
  · intro ⟨h0,h1⟩ h2
    exact h1 (le_antisymm a b h0 h2)
  tfae_have 2 → 3
  · intro h0
    have h2 := Or.resolve_right (le_total a b) h0
    rcases h2 with ⟨n,hn⟩
    cases n with l
    · rw [hn,add_zero] at h0
      exact False.elim (h0 (le_refl a))
    use l
    rw [hn,add_succ,succ_add]
    rfl
  tfae_have 3 → 4
  · intro ⟨nn,hnn⟩
    use nn
    rw [←hnn,succ_add]
    rfl
  tfae_have 4 → 5
  · intro ⟨n,hn⟩
    use n
    rw [←hn]
    rw [add_succ]
    rfl
  tfae_have 5 → 6
  · rintro ⟨n,h0⟩
    use n
    rw [←h0,add_succ,succ_add]
    rfl
  tfae_have 6 → 1
  · intro ⟨c,hc⟩
    constructor
    use succ c
    rw [hc,add_succ,succ_add]
    rfl
    intro h1
    rw [h1,succ_add,←add_succ] at hc
    have h2 : succ c = 0 := add_right_eq_self b (succ c) hc.symm
    exact (succ_ne_zero c) h2
  tfae_finish


TheoremTab "<"
