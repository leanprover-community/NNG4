import Game.Levels.LessThan.A_L09_lt_succ_iff_le
  

World "LessThan"
Level 10
Title "We can cancel a addend from both sides of a strict equality"

TheoremTab "<"

namespace MyNat

/-- We can cancel an addend from both sides of an inequality -/

TheoremDoc MyNat.lt_of_add_lt_add_left as "lt_of_add_lt_add_left" in "<"

Introduction ""

/-- explanation -/
Statement lt_of_add_lt_add_left (a b c : ℕ) : a + b < a + c → b < c := by --level 10
  intro ⟨n,hn⟩
  rw [succ_add,add_assoc,←add_succ,←add_succ] at hn
  have h1 := add_left_cancel c (b + succ n) a hn
  use n
  rw [h1,add_succ,succ_add]
  rfl

Conclusion "CONCLUSION"
