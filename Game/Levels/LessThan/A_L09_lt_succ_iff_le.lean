import Game.Levels.LessThan.A_L08_succ_le_succ_iff

World "LessThan"
Level 9
Title "m < succ n ↔ m ≤ n"

TheoremTab "<"

namespace MyNat

/-- `lt_succ_iff_le m n` is a proof that `m < succ n` iff `m ≤ n`.-/
TheoremDoc MyNat.lt_succ_iff_le as "lt_succ_iff_le" in "<"

Introduction "In this level we show that `m < succ n ↔ m ≤ n`.  In
words a a number `m` is less than `n`'s sucessor if and only if `m` is
less than or equal to `n`.  This is a useful theorem in the following
levels."


/-- `lt_succ_iff_le m n` is a proof that `m < succ n ↔ m ≤ n`-/
Statement lt_succ_iff_le (m n : ℕ) : m < succ n ↔ m ≤ n := by
  Hint (hidden := true) "Try to rewrite the right hand side using succ_le_succ_iff."
  rw [←succ_le_succ_iff m n]
  apply Iff.intro
  intro h0
  exact h0
  intro h0
  exact h0

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

Conclusion
"My proof
```
  rw [←succ_le_succ_iff m n]
  apply Iff.intro
  intro h0
  exact h0
  intro h0
  exact h0
```
"

