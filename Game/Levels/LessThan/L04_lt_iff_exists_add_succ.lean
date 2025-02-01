import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual
import Game.Levels.LessThan.L03_lt_iff_not_le

World "LessThan"
Level 4
Title "The `use` tactic"

namespace MyNat






/--
`lt_iff_not_le a b` is a proof of `a < b ↔ ¬(b  ≤ x)`.

The reason for the name is that this lemma is "reflexivity of $\le$"
-/
TheoremDoc MyNat.lt_iff_exists_add_succ as "lt_iff_exists_add_succ" in "<"

/-- If $x$ is a number, then $x \le x$. -/
Statement lt_iff_exists_add_succ (a b: ℕ) : a < b ↔ ∃ c : MyNat, b = a + c.succ:= by
  apply Iff.intro
  rintro ⟨⟨c,h1⟩,h2⟩
  cases c with d
  exfalso
  rw [add_zero] at h1
  exact h2 h1.symm
  use d
  rw [h1]
  rfl
  intro ⟨c,hc⟩
  apply And.intro
  use succ c
  exact hc
  intro hab
  rw [hab] at hc
  have h1 : succ c = 0 :=  add_right_eq_self b (succ c) hc.symm
  have h2 := succ_ne_zero c
  exact h2 h1


TheoremTab "<"
