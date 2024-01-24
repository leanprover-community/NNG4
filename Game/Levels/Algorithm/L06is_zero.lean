import Game.Levels.Algorithm.L05pred

World "Algorithm"
Level 6
Title "is_zero"

TheoremTab "Peano"

namespace MyNat

Introduction
"
We define a function `is_zero` thus:

```
is_zero 0 := True
is_zero (succ n) := False
```

We also create two lemmas, `is_zero_zero` and `is_zero_succ n`, saying that `is_zero 0 = True`
and `is_zero (succ n) = False`. Let's use these lemmas to prove `succ_ne_zero`, Peano's
Last Axiom. Actually, we have been using `zero_ne_succ` before, but it's handy to have
this opposite version too, which can be proved in the same way. Note: you can
cheat here by using `zero_ne_succ` but the point of this world is to show
you how to *prove* results like that.

If you can turn your goal into `True`, then the `triv` tactic will solve it.
"

/-- `is_zero_zero` is a proof of `is_zero 0 = True`. -/
TheoremDoc MyNat.is_zero_zero as "is_zero_zero" in "Peano"

/-- `is_zero_succ a` is a proof of `is_zero (succ a) = False`. -/
TheoremDoc MyNat.is_zero_succ as "is_zero_succ" in "Peano"

/-- `succ_ne_zero a` is a proof of `succ a ≠ 0`. -/
TheoremDoc MyNat.succ_ne_zero as "succ_ne_zero" in "Peano"

NewTheorem MyNat.is_zero_zero MyNat.is_zero_succ

/--
# Summary

`triv` will solve the goal `True`.
-/
TacticDoc triv


NewTactic triv

/-- $\operatorname{succ}(a) \neq 0$. -/
Statement succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  Hint "Start with `intro h` (remembering that `X ≠ Y` is just notation
  for `X = Y → False`)."
  intro h
  Hint "We're going to change that `False` into `True`. Start by changing it into
  `is_zero (succ a)` by executing `rw [← is_zero_succ a]`."
  rw [← is_zero_succ a]
  Hint "See if you can take it from here. Look at the new lemmas and tactic
  available on the right."
  rw [h]
  rw [is_zero_zero]
  triv
