import Game.Levels.Addition
import Game.MyNat.AdvAddition

World "AdvAddition"
Level 1
Title "The `assumption` tactic"

namespace MyNat

TacticDoc assumption "
## Summary

This tactic closes the goal if the goal is *identically* one
of the assumptions.

### Example

If the goal is `x = 37` and you have a hypothesis `main_result_2 : x = 37`
then `assumption` will solve the goal.
"

NewTactic assumption

Introduction
"
In this world we'll learn how to prove theorems of the form $P\\implies Q$.
To do that we need to learn some more tactics.

The `assumption` tactic closes a goal if it is identical to
one of our hypotheses.
"

/-- Assuming $x+y=37$ and $3x+z=42$, we have $x+y=37$. -/
Statement (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  Hint "The goal is one of our hypotheses. Solve the goal by casting `assumption`."
  assumption
