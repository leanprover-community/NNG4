import Game.Levels.Implication.L09zero_ne_succ
World "Implication"
Level 10
Title "1 ≠ 0"

LemmaTab "012"

namespace MyNat

Introduction "
We know `zero_ne_succ n` is a proof of `0 = succ n → False` -- but what
if we have a hypothesis `succ n = 0`? It's the wrong way around!

The `symm` tactic changes a goal `x = y` to `y = x`, and a goal `x ≠ y`
to `y ≠ x`. And `symm at h`
does the same for a hypothesis `h`. We've proved $0 \\neq 1$ and called
the proof `zero_ne_one`; now try proving $1 \\neq 0$.
"

TacticDoc symm "
## Summary

The `symm` tactic will change a goal or hypothesis of
the form `X = Y` to `Y = X`. It will also work on `X ≠ Y`
and on `X ↔ Y`.

### Example

If the goal is `2 + 2 = 4` then `symm` will change it to `4 = 2 + 2`.

### Example

If `h : 2 + 2 ≠ 5` then `symm at h` will change `h` to `5 ≠ 2 + 2`.
"

NewTactic symm

LemmaDoc MyNat.one_ne_zero as "one_ne_zero" in "012" "
`one_ne_zero` is a proof that `1 ≠ 0`."

/-- $1\neq0$. -/
Statement one_ne_zero : (1 : ℕ) ≠ 0 := by
  symm
  exact zero_ne_one

Conclusion "What do you think of this two-liner:
```
symm
exact zero_ne_one
```

`exact` doesn't just take hypotheses, it will eat any proof which exists
in the system.
"
