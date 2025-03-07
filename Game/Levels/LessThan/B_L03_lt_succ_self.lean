import Game.Levels.LessThan.B_L02_succ_succ_eq_succ_succ_iff

World "LessThan"
Level 3
Title "lt_succ_self"

namespace MyNat


/-- `a < b` is *notation* for `succ a ≤ b`, and 'succ a ≤ b` in turn
is *notation* for `∃ c : b = succ a + c`.  This mean that if you have
a *goal* of the for `a < b`, you can make progress with the `use
tactice`, and if you have a *hypothesis* (h : a < b) you can make
progress with `cases h with c hc`.  -/
DefinitionDoc LT as "<"

Introduction "In the `≤` world, we showed that `≤` is reflexive
relation.  In this world our first task is to show that ̀`<` is an
*ir*reflexive relation.  An irreflexive relation is one for which no
element is related to itself.

Remember that `a<b` is notation for `succ a ≤ b`, And that `succ a ≤
b` is itself notation for \"there exists `c` such that `b = succ a +
c`\".  As such, we can make progress on goals of the form `a < b` by
`use`ing the number which is morally `b - succ a` (i.e. `use b - succ
a`).

Of course we haven't defined subtraction so deciphering which
expression is morally equal to this difference will be your task."

/-- `lt_succ_self a` is a proof that `a < succ a` -/
TheoremDoc MyNat.lt_succ_self as "lt_succ_self" in "<"


/-- If `a` is a natural number, then `a < succ a` -/
Statement lt_succ_self (a : ℕ) : a < succ a := by
  use 0
  rw [add_zero]
  rfl

Conclusion "CONCLUSION."
