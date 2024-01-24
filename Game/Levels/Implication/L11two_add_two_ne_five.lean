import Game.Levels.Implication.L10one_ne_zero

World "Implication"
Level 11
Title "2 + 2 ≠ 5"

TheoremTab "Peano"

namespace MyNat

Introduction
" 2 + 2 ≠ 5 is boring to prove in full, given only the tools we have currently.
To make it a bit less painful, I have unfolded all of the numerals for you.
See if you can use `zero_ne_succ` and `succ_inj` to prove this.
"

/-- $2+2≠5$. -/
Statement : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  intro h
  rw [add_succ, add_succ, add_zero] at h
  repeat apply succ_inj at h
  apply zero_ne_succ at h
  exact h

Conclusion "Here's my proof:
```
intro h
rw [add_succ, add_succ, add_zero] at h
repeat apply succ_inj at h
apply zero_ne_succ at h
exact h
```

Even though Lean is a theorem prover, right now it's pretty clear that we have not
developed enough material to make it an adequate calculator. In Algorithm
World, a more computer-sciency world, we will develop machinery which makes
questions like this much easier, and goals like $20 + 20 ≠ 41$ feasible.
Alternatively you can do more mathematics in Advanced Addition World, where we prove
the lemmas needed to get a working theory of inequalities. Click \"Leave World\" and
decide your route."
