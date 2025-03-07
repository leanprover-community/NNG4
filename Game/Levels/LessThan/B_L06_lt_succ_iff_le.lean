import Game.Levels.LessThan.B_L05_lt_iff_le_not_le

World "LessThan"
Level 6
Title "lt_succ_iff_le"

namespace MyNat

/-- `lt_succ_iff_le m n `is a proof that `m < succ n ↔ m ≤ n` -/
TheoremDoc MyNat.lt_succ_iff_le as "lt_succ_iff_le" in "<"

Introduction "In this level, "

/--If `m` and `n` are natural numbers, then `lt_succ_iff_le m n` is a proof
that `m < succ n ↔ m ≤ n`.-/
Statement lt_succ_iff_le (m n : ℕ) : m < succ n ↔ m ≤ n := by 
  apply Iff.intro
  intro ⟨k,hk⟩
  rw [succ_add] at hk
  have hk1 := succ_inj n (m + k) hk
  exact Exists.intro k hk1
  intro ⟨k,hk⟩
  use k
  rw [hk]
  rw [succ_add]
  rfl



Conclusion "CONCLUSION."






