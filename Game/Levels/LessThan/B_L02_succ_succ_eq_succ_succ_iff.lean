import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual
import Game.Levels.LessThan.B_L01_succ_eq_succ_iff

World "LessThan"
Level 2
Title "Practice with `rw`"

namespace MyNat

Introduction "In this level, you will get practice using the `rw`
tactic with iff statements.  Before this level, you used `rw` to
substitute equations into the goal or into other expressions.  The `rw` tactic
can be used to rewrite equivalent propositions into each other in the same way."

/-- YADDA We don't really want this as a theorem do we.  TODO: Check how the other intro
levels were handled. -/
TheoremDoc MyNat.succ_succ_eq_succ_succ_iff as "succ_succ_eq_succ_succ_iff" in "<"

/--Equal numbers have equal successors of successors and vice versa.-/
Statement succ_succ_eq_succ_succ_iff (a b : ℕ) :
  succ (succ a) = succ (succ b) ↔ a = b := by
  Hint "To strip of one pair of `succ`'s, you can use `rw [succ_eq_succ_iff]`."
  rw [succ_eq_succ_iff]

  Hint "Now strip off the next pair of `succ`'s."
  rw [succ_eq_succ_iff]
  Hint "We have something of the form `p ↔ p`, which can be solved with `rfl`."
  rfl

Conclusion "A different proof
```
  rw [succ_eq_succ_iff]
  exact (succ_eq_succ_iff a b)
```
"










