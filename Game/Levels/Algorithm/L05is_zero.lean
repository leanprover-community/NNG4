import Game.Levels.Algorithm.L04pred

World "Algorithm"
Level 5
Title "is_zero"

LemmaTab "Peano"

namespace MyNat

Introduction
"
We now define a function `is_zero` thus:

```
is_zero 0 := True
is_zero (succ n) := False
```

We also need two lemmas, `is_zero_zero` and `is_zero_succ`, saying that `is_zero 0 = True`
and `is_zero (succ n) = False`. Let's use this function to prove `succ_ne_zero`, Peano's
Last Axiom. We have been using `zero_ne_succ` before, but it's handy to have
this opposite version too.

If you can turn your goal into `True`, then the `tauto` tactic will solve it.
"

LemmaDoc MyNat.is_zero_zero as "is_zero_zero" in "Peano"
"
`is_zero_zero` is a proof of `is_zero 0 = True`.
"

LemmaDoc MyNat.is_zero_succ as "is_zero_succ" in "Peano"
"
`is_zero_succ a` is a proof of `is_zero (succ a) = False`.
"

LemmaDoc MyNat.succ_ne_zero as "succ_ne_zero" in "Peano"
"
`succ_ne_zero a` is a proof of `succ a ≠ 0`.
"

NewLemma MyNat.is_zero_zero MyNat.is_zero_succ

/-- If $\operatorname{succ}(a)=\operatorname{succ}(b)$ then $a=b$. -/
Statement succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  Hint "Start with `intro h`."
  intro h
  Hint "We're going to change that `False` into `True`. Start by changing it into `is_zero (succ a)`."
  Hint (hidden := true) "Try `rw [← is_zero_succ a]`."
  rw [← is_zero_succ a]
  rw [h]
  rw [is_zero_zero]
  tauto
