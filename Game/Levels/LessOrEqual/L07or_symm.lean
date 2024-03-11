import Game.Levels.LessOrEqual.L06le_antisymm

World "LessOrEqual"
Level 7
Title "Dealing with `or`"

namespace MyNat

TheoremTab "≤"

/--
# Summary
The `left` tactic changes a goal of `P ∨ Q` into a goal of `P`.
Use it when your hypotheses guarantee that the reason that `P ∨ Q`
is true is because in fact `P` is true.

Internally this tactic is just `apply`ing a theorem
saying that $P \implies P \lor Q.$

Note that this tactic can turn a solvable goal into an unsolvable
one.
-/
TacticDoc left

/--
# Summary
The `right` tactic changes a goal of `P ∨ Q` into a goal of `Q`.
Use it when your hypotheses guarantee that the reason that `P ∨ Q`
is true is because in fact `Q` is true.

Internally this tactic is just `apply`ing a theorem
saying that $Q \implies P \lor Q.$

Note that this tactic can turn a solvable goal into an unsolvable
one.
-/
TacticDoc right


NewTactic left right

Introduction "
Totality of `≤` is the boss level of this world, and it's coming up next. It says that
if `a` and `b` are naturals then either `a ≤ b` or `b ≤ a`.
But we haven't talked about `or` at all. Here's a run-through.

1) The notation for \"or\" is `∨`. You won't need to type it, but you can
type it with `\\or`.

2) If you have an \"or\" statement in the *goal*, then two tactics made
progress: `left` and `right`. But don't choose a direction unless your
hypotheses guarantee that it's the correct one.

3) If you have an \"or\" statement as a *hypothesis* `h`, then
`cases h with h1 h2` will create two goals, one where you went left,
and the other where you went right.
"

/-- If $x=37$ or $y=42$, then $y=42$ or $x=37$. -/
Statement (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  Hint "We don't know whether to go left or right yet. So start with `cases h with hx hy`."
  cases h with hx hy
  Hint "Now we can prove the `or` statement by proving the statement on the right,
  so use the `right` tactic."
  right
  exact hx
  Hint (hidden := true) "This time, use the `left` tactic."
  left
  exact hy

TheoremTab "≤"

Conclusion "
Ready for the boss level of this world?
"
