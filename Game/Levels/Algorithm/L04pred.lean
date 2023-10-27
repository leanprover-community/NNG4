import Game.Levels.Algorithm.L03add_algo2
import Game.Levels.Implication

World "Algorithm"
Level 4
Title "pred"

LemmaTab "Peano"

namespace MyNat

Introduction
"
We now start work on an algorithm to do addition more efficiently. Recall that
we defined addition by recursion, saying what it did on `0` and successors.
It is an axiom of Lean that recursion is a valid
way to define functions from types such as the naturals.

Let's define a new function `pred` from the naturals to the naturals, which
attempts to subtract 1 from the input. The definition is this:

```
pred 0 := 37
pred (succ n) := n
```

We cannot subtract one from 0, so we just return a junk value. A new lemma `pred_succ`
says that `pred (succ n) = n`. Let's use it to prove `succ_inj`, the theorem which
Peano assumed as an axiom and which we have already used extensively without justification.
"

LemmaDoc MyNat.pred_succ as "pred_succ" in "Peano"
"
`pred_succ n` is a proof of `pred (succ n) = n`.
"

NewLemma MyNat.pred_succ

/-- If $\operatorname{succ}(a)=\operatorname{succ}(b)$ then $a=b$. -/
Statement (a b : ℕ) (h : succ a = succ b) : a = b := by
  Hint "Start with `rw [← pred_succ a]` and take it from there."
  rw [← pred_succ a]
  rw [h]
  rw [pred_succ]
  rfl

Conclusion
"Let's now prove Peano's other axiom, `zero_ne_succ`.
"
