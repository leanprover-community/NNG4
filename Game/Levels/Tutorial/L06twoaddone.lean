import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial.L03three_eq_sss0
World "Tutorial"
Level 6
Title "2+1=3"

open MyNat

Introduction
" First you need to face the sub-boss `2 + 1 = 3`.
"
namespace MyNat

/-- $2+2=4$. -/
Statement two_add_one_eq_three : (2 : ℕ) + 1 = 3 := by
  Hint (hidden := true) "`rw [one_eq_succ_zero]` unlocks `add_succ`"
  rw [one_eq_succ_zero]
  Hint (hidden := true) "Now you can `rw [add_succ]`"
  rw [add_succ]
  rw [add_zero]
  rw [three_eq_succ_two]
  rfl

LemmaDoc MyNat.two_add_one_eq_three as "two_add_one_eq_three" in "Add"
"`two_add_one` is the proof of `2 + 1 = 3`."

NewLemma MyNat.two_add_one_eq_three
LemmaTab "Add"


Conclusion
"
  Do you think you're ready for `2 + 2 = 4`?
"
