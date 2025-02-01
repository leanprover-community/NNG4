import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual

World "LessThan"
Level 3
Title "The `use` tactic"

namespace MyNat





/--
`lt_iff_not_le a b` is a proof of `a < b ↔ ¬(b  ≤ x)`.

The reason for the name is that this lemma is "reflexivity of $\le$"
-/
TheoremDoc MyNat.lt_iff_not_le as "lt_iff_not_le" in "<"

/-- If $a\ b$ are natural numbers the a < b ↔ ¬(b ≤ a)
-/
Statement lt_iff_not_le (a b: ℕ) : a < b ↔ ¬(b ≤ a):= by
  apply Iff.intro
  intro ⟨h0,h1⟩ h2
  exact h1 (le_antisymm a b h0 h2)
  intro h0
  have h2 := Or.resolve_right (le_total a b) h0
  rcases h2 with ⟨n,hn⟩
  rw [hn] at h0
  cases n with l
  rw [add_zero] at h0
  exfalso
  exact h0 (le_refl a)
  rw [hn]
  constructor
  use succ l
  rfl
  intro h1
  have h2 :=add_right_eq_self a (succ l) h1.symm
  exact (succ_ne_zero l) h2



TheoremTab "<"
