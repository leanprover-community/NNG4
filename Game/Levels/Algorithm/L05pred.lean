import Game.Levels.Algorithm.L04add_algo3
import Game.Levels.Implication

World "Algorithm"
Level 5
Title "pred"

TheoremTab "Peano"

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

We cannot subtract one from 0, so we just return a junk value. As well as this
definition, we also create a new lemma `pred_succ`, which says that `pred (succ n) = n`.
Let's use this lemma to prove `succ_inj`, the theorem which
Peano assumed as an axiom and which we have already used extensively without justification.
"

TheoremDoc MyNat.pred_succ as "pred_succ" in "Peano"
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
"
Nice! You've proved `succ_inj`!
Let's now prove Peano's other axiom, that successors can't be $0$.
"
