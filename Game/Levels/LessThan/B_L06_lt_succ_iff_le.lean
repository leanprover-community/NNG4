import Game.Levels.LessThan.B_L05_lt_iff_le_not_le

World "LessThan"
Level 6
Title "lt_succ_iff_le"

namespace MyNat

/-- `lt_succ_iff_le m n `is a proof that `m < succ n ↔ m ≤ n` -/
TheoremDoc MyNat.lt_succ_iff_le as "lt_succ_iff_le" in "<"

Introduction "You are building up to fight the final boss of this world, Strong Induction.
Your task in this level is to show that `m < succ n ↔ m ≤ n`.  The proof is straightforward
so you probably don't need any hints."

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






