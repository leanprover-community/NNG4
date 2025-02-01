import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual
import Game.Levels.LessThan.L04_lt_iff_exists_add_succ

World "LessThan"
Level 5
Title ""

namespace MyNat

/--
something
-/
TheoremDoc MyNat.lt_iff_succ_le as "lt_iff_succ_le" in "<"

/-- Blah
-/
Statement lt_iff_succ_le (a b: ℕ) : a < b ↔ a.succ ≤ b:= by
  apply Iff.intro
  intro ⟨⟨c,hc⟩,h1⟩
  cases c with ll
  exfalso
  rw [add_zero] at hc
  exact h1 (hc.symm)
  use ll
  rw [hc,succ_add,add_succ]
  rfl
  intro ⟨c,h0⟩
  rw [succ_add] at h0
  rw [←add_succ] at h0
  rw [h0]
  constructor
  use succ c
  rfl
  intro h1
  have h3 : succ c = 0 := sorry
  have h4 := succ_ne_zero c
  exact h4 h3

TheoremTab "<"
