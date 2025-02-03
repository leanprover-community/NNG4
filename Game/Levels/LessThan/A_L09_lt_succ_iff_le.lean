import Game.Levels.LessThan.A_L08_succ_le_succ

World "LessThan"
Level 9
Title "m < succ n ↔ m ≤ n"

TheoremTab "<"

namespace MyNat

/-- `lt_succ_iff_le m n` is a proof that `m < succ n` iff `m ≤ n`.-/
TheoremDoc MyNat.lt_succ_iff_le as "lt_succ_iff_le" in "<"

Introduction "INTRODUCTION"

/-- `lt_succ_iff_le m n` is a proof that `m < succ n ↔ m ≤ n`-/
Statement lt_succ_iff_le (m n : ℕ) : m < succ n ↔ m ≤ n := by -- Level 09
  rw [←succ_le_succ_iff m n]
  apply Iff.intro
  exact id
  exact id

  -- Old proof
  -- constructor
  -- rintro ⟨k,hk⟩
  -- rw [succ_add] at hk
  -- have hk1 := succ_inj n (m + k) hk
  -- use k
  -- exact hk1
  -- rintro ⟨k,hk⟩
  -- use k
  -- rw [hk]
  -- rw [succ_add]
  -- rfl

Conclusion "CONCLUSION"
