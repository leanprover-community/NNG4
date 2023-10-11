import Game.Levels.Implication.L11two_add_two_ne_five

World "AdvAddition"
Level 1
Title "ne_succ_self"

LemmaTab "Peano"

namespace MyNat

Introduction
"In this world I will mostly leave you on your own.
However I'll give you a couple of hints for this first level,
which is a warm-up to see if you remember `zero_ne_succ`
and `succ_inj`, and how to use the `apply` tactic.
"

/-- $n\neq\operatorname{succ}(n)$. -/
Statement ne_succ_self (n : ℕ) : n ≠ succ n := by
  Hint "Start with `induction`."
  induction n with d hd
  Hint (hidden := true) "Now you can do `intro, apply, exact`, but `exact zero_ne_succ 0` will work."
  exact zero_ne_succ 0
  intro h
  apply succ_inj at h
  apply hd at h
  exact h

Conclusion "How about this for a proof:

```
induction n with d hd
-- base case can be done in one line
exact zero_ne_succ 0
-- inductive step
intro h
apply succ_inj at h
apply hd at h -- remember `hd : d = succ d → False`
exact h
```
"
