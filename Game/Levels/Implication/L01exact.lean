import Game.Levels.Addition
import Game.MyNat.PeanoAxioms

World "Implication"
Level 1
Title "The `exact` tactic"

namespace MyNat

TacticDoc exact "
## Summary

If the goal is a statement `P`, then `exact h` will close the goal if `h` is a proof of `P`.

### Example

If the goal is `x = 37` and you have a hypothesis `h : x = 37`
then `exact h` will solve the goal.

### Example

If the goal is `x + 0 = x` then `exact add_zero x` will close the goal.

### Exact needs to be exactly right

Note that `exact add_zero` will *not work* in the previous example;
for `exact h` to work, `h` has to be *exactly* a proof of the goal.
`add_zero` is a proof of `∀ n, n + 0 = n` or, if you like,
a proof of `? + 0 = ?` where `?` needs to be supplied by the user.
This is in contrast to `rw` and `apply`, which will \"guess the inputs\"
if necessary. If the goal is `x + 0 = x` then `rw [add_zero]`
and `rw [add_zero x]` will both change the goal to `x = x`,
because `rw` guesses the input to the function `add_zero`.
"

NewTactic exact

Introduction
"
In this world we'll learn how to prove theorems of the form $P\\implies Q$.
To do that we need to learn some more tactics.

The `exact` tactic can be used to close a goal which is exactly one of
the hypotheses.
"

/-- Assuming $x+y=37$ and $3x+z=42$, we have $x+y=37$. -/
/-
When buildint this generates a warning
unused variable `h2` [linter.unusedVariables]
but I want `h2` to be there.
-/
Statement (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  Hint "The goal is one of our hypotheses. Solve the goal by executing `exact h1`."
  exact h1
