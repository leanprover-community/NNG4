import Game.Levels.LessThan.A_L03_not_lt_zero

World "LessThan"
Level 4
Title "a < b → b ≤ c → a < c"

TheoremTab "<"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.lt_of_lt_of_le as "lt_of_lt_of_le" in "<"

Introduction "INTRO"

/-- If a < b and b ≤ c then a < c -/
Statement lt_of_lt_of_le (a b c: ℕ) : a < b → b ≤ c → a < c := by
  rintro ⟨n,hnab⟩ ⟨m,hmbc⟩
  use (n + m)
  rw [hmbc,hnab,add_assoc]
  rfl

Conclusion "CONCLUSION"
