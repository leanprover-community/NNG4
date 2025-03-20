import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition


World "LessThan"
Level 1
Title "Successor are equal iff originals are equal"

namespace MyNat

/--
## Summary

The `constructor` tactic can be used to split a compound goal into its 
parts.

## Example
If you have a goal of the form `p ↔ q`, and you execute
`constructor`, then you will replace `p ↔ q` with two goals, first
`p →  q` and then `q`→ p`.


## Example
If you have a goal of the form `p ∧ q`, and you execute
`constructor`, then you will get replace `p ∧ q` with two goals,
first `p` and then `q`.
-/
TacticDoc constructor

NewTactic constructor

Introduction "In this level we introduce a tactic that will be useful
in this world, the `constructor` tactic.  For two proposition `p` and
`q`, `p ↔ q`, consists of two statements (1) the Modus Ponens: `p → q`
and (2) the reversed Modus Ponens: `q → p`.  If you have a goal of the
form `p ↔ q`, then the `constructor` tactic will split this goal into
these two sub-goals.

We practice using this tactic in this level."


/--`succ_eq_succ_iff a b` is a proof that `succ a = succ b ↔ a = b`.  In words,
  equal numbers have equal successors and vice versa.
-/
TheoremDoc MyNat.succ_eq_succ_iff as "succ_eq_succ_iff" in "<"

/-- If `a b` are natural numbers, then `succ a = succ b ↔ a = b` -/
Statement  succ_eq_succ_iff (a b : ℕ) : succ a = succ b ↔ a = b := by
  Hint"The goal is an iff statement so use `constructor`."
  constructor
  Hint "The `succ_inj` theorem is useful here."
  intro h0
  have h1 := succ_inj a b h0
  exact h1
  intro h0
  rw [h0]
  rfl

TheoremTab "<"

Conclusion "The `constructor` tactic also works on goals of the form `P
∧ Q`, for two propositions `P` and `Q`.

Now you know how to construct an iff statement from two implications,
in the next level how to use the `rw` tactic with `↔` statements."
