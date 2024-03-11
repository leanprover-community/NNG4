import Game.Levels.Implication.L05succ_inj2

World "Implication"
Level 6
Title "intro"

namespace MyNat

/--
## Summary

If the goal is `P → Q`, then `intro h` will introduce `h : P` as a hypothesis,
and change the goal to `Q`. Mathematically, it says that to prove $P \implies Q$,
we can assume $P$ and then prove $Q$.

### Example:

If your goal is `x + 1 = y + 1 → x = y` (the way Lean writes $x+1=y+1 \implies x=y$)
then `intro h` will give you a hypothesis $x+1=y+1$ named `h`, and the goal
will change to $x=y$.
-/
TacticDoc intro

NewTactic intro


Introduction
"We have seen how to `apply` theorems and assumptions
of the form `P → Q`. But what if our *goal* is of the form `P → Q`?
To prove this goal, we need to know how to say \"let's assume `P` and deduce `Q`\"
in Lean. We do this with the `intro` tactic.
"

/-- $x=37\implies x=37$. -/
Statement (x : ℕ) : x = 37 → x = 37 := by
  Hint "Start with `intro h` to assume the hypothesis and call its proof `h`."
  intro h
  Hint (hidden := true) "Now `exact h` finishes the job."
  exact h
