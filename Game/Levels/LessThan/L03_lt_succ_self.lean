import Game.Levels.LessThan.L02_succ_succ_eq_succ_succ_iff

World "LessThan"
Level 3
Title "lt_succ_self"

namespace MyNat


/-- `a < b` is *notation* for `succ a ≤ b`, and `succ a ≤ b` in turn
is *notation* for `∃ c : b = succ a + c`.  This mean that if you have
a *goal* of the for `a < b`, you can make progress with the `use
tactice`, and if you have a *hypothesis* (h : a < b) you can make
progress with `cases h with c hc`.  -/
DefinitionDoc LT as "<"

NewDefinition LT

Introduction "In this level we define a new relation, `<`, on the
natural numbers,  For `a b`, two natural number, we have
`a < b` if (and only if) `succ a ≤ b`.  

Remember that that `succ a ≤
b` is notation for \"there exists `c` such that `b = succ a +
c`\".  As such, we can make progress on goals of the form `a < b` by
`use`ing the number which is morally `b - succ a` (i.e. `use (b - succ
a)`).

Of course we haven't defined subtraction yet so deciphering which
expression is morally equal to this difference will be your task.

We start by showing every number is less than its sucessor."

/-- `lt_succ_self a` is a proof that `a < succ a` -/
TheoremDoc MyNat.lt_succ_self as "lt_succ_self" in "<"


/-- If `a` is a natural number, then `a < succ a` -/
Statement lt_succ_self (a : ℕ) : a < succ a := by
  Hint "Remember that `lhs < rhs` is defined as `succ lhs ≤ rhs`.  How
  would you show this for the cases when `lhs = a` and `rhs = succ
  a`?"
  use 0
  rw [add_zero]
  rfl

Conclusion "Nice job.  In the next level you will show that the
relations \"less than:`<`\"  and \"less than or equal:`≤`\" make linguistic
as well as mathematical sense."
