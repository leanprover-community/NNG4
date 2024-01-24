import Game.Levels.Implication.L02exact2

World "Implication"
Level 3
Title "The `apply` tactic."

namespace MyNat

TheoremTab "Peano"

TacticDoc apply "
## Summary

If `t : P → Q` is a proof that $P\\implies Q$, and `h : P` is a proof of `P`,
then `apply t at h` will change `h` to a proof of `Q`. The idea is that if
you know `P` is true, then you can deduce from `t` that `Q` is true.

If the *goal* is `Q`, then `apply t` will \"argue backwards\" and change the
goal to `P`. The idea here is that if you want to prove `Q`, then by `t`
it suffices to prove `P`, so you can reduce the goal to proving `P`.

### Example:

`succ_inj x y` is a proof that `succ x = succ y → x = y`.

So if you have a hypothesis `h : succ (a + 37) = succ (b + 42)`
then `apply succ_inj at h` will change `h` to `a + 37 = b + 42`.
You could write `apply succ_inj (a + 37) (b + 42) at h`
but Lean is smart enough to figure out the inputs to `succ_inj`.

### Example

If the goal is `a * b = 7`, then `apply succ_inj` will turn the
goal into `succ (a * b) = succ 7`.
"
NewTactic apply

Introduction
"
In this level one of our hypotheses is an *implication*. We can use this
hypothesis with the `apply` tactic.
"

/-- If $x=37$ and we know that $x=37\implies y=42$ then we can deduce $y=42$. -/
Statement (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  Hint "Start with `apply h2 at h1`. This will change `h1` to `y = 42`."
  apply h2 at h1
  Hint "Now finish using the `exact` tactic."
  exact h1
