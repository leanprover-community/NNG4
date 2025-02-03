import Game.Levels.LessThan.A_L05_lt_of_le_of_lt

World "LessThan"
Level 6
Title "less than is a transitive relation"

TheoremTab "<"

namespace MyNat

/--`lt_trans a b c` is a proof that if `a < b` then (`b < c` implies `a < c`)-/
TheoremDoc MyNat.lt_trans as "lt_trans" in "<"

Introduction "INTRO"

/-- If a < b and b < c, then a < c -/
Statement lt_trans (a b c : ℕ) : a < b → b < c → a < c := by
  intro ⟨n,hnab⟩ ⟨m,hmbc⟩
  use (succ (n + m))
  rw [hmbc,hnab]
  repeat rw [succ_add]
  rw [add_succ,add_assoc]
  rfl

Conclusion "CONCLUSION"
