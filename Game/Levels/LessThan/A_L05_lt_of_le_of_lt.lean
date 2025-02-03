import Game.Levels.LessThan.A_L04_lt_of_lt_of_le

World "LessThan"
Level 5
Title "lt_of_le_of_lt"

TheoremTab "<"

namespace MyNat

/--
`lt_of_le_of_lt x y z` is a proof that if `x ≤ y` and `y < z` then `x < z`.
More precisely, it is a proof that `x ≤ y → (y < z → x< z)`. In words,
If $x \le y$ then (pause) if $y < z$ then $x < z$.-/
TheoremDoc MyNat.lt_of_le_of_lt as "lt_of_le_of_lt" in "<"

Introduction "INTRO"

/-- If `a ≤ b` and `b < c` then `a < c`. -/
Statement lt_of_le_of_lt (a b c : ℕ) : a ≤ b → b < c → a < c := by
  intro ⟨n,hnab⟩ ⟨m,hmbc⟩
  use (n + m)
  rw [hmbc,hnab]
  repeat rw [succ_add]
  rw [add_assoc]
  rfl

Conclusion "CONCLUSION"
