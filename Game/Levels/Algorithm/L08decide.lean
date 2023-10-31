import Game.Levels.Algorithm.L07succ_ne_succ
import Game.MyNat.DecidableEq

World "Algorithm"
Level 8
Title "decide"

LemmaTab "Peano"

namespace MyNat

TacticDoc decide "
# Summary

`decide` will attempt to solve a goal if it can find an algorithm which it
can run to solve it.

## Example

A term of type `DecidableEq ℕ` is an algorithm to decide whether two naturals
are equal or different. Hence, once this term is made and made into an `instance`,
the `decide` tactic can use it to solve goals of the form `a = b` or `a ≠ b`.
"

NewTactic decide

Introduction
"
Implementing the algorithm for equality of naturals, and the proof that it is correct,
looks like this:

```
instance instDecidableEq : DecidableEq ℕ
| 0, 0 => isTrue <| by
  show 0 = 0
  rfl
| succ m, 0 => isFalse <| by
  show succ m ≠ 0
  exact succ_ne_zero m
| 0, succ n => isFalse <| by
  show 0 ≠ succ n
  exact zero_ne_succ n
| succ m, succ n =>
  match instDecidableEq m n with
  | isTrue (h : m = n) => isTrue <| by
    show succ m = succ n
    rw [h]
    rfl
  | isFalse (h : m ≠ n) => isFalse <| by
    show succ m ≠ succ n
    exact succ_ne_succ m n h
```

This Lean code is a formally verified algorithm for deciding equality
between two naturals. Run it with the `decide` tactic.
"

/-- $20+20=40$. -/
Statement : (20 : ℕ) + 20 = 40 := by
  MyDecide

Conclusion "You can read more about the `decide` tactic by clicking
on it in the top right."
