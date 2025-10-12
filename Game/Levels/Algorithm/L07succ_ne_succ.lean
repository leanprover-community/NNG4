import Game.Levels.Algorithm.L06is_zero

World "Algorithm"
Level 7
Title "An algorithm for equality"

TheoremTab "Peano"

namespace MyNat

Introduction
"
Here we begin to
develop an algorithm which, given two naturals `a` and `b`, returns the answer
to \"does `a = b`?\"

Here is the algorithm. First note that `a` and `b` are numbers, and hence
are either `0` or successors.

*) If `a` and `b` are both `0`, return \"yes\".

*) If one is `0` and the other is `succ n`, return \"no\".

*) If `a = succ m` and `b = succ n`, then return the answer to \"does `m = n`?\"

Our job now is to *prove* that this algorithm always gives the correct answer. The proof that
`0 = 0` is `rfl`. The proof that `0 ≠ succ n` is `zero_ne_succ n`, and the proof
that `succ m ≠ 0` is `succ_ne_zero m`. The proof that if `h : m = n` then
`succ m = succ n` is `rw [h]` and then `rfl`. This level is a proof of the one
remaining job we have to do: if `a ≠ b` then `succ a ≠ succ b`.
"

/--
# Summary

If you have a hypothesis

`h : a ≠ b`

and goal

`c ≠ d`

then `contrapose! h` replaces the set-up with its so-called \"contrapositive\":
a hypothesis

`h : c = d`

and goal

`a = b`.
-/
TacticDoc contrapose

NewTactic contrapose
NewHiddenTactic contrapose!

/-- `succ_ne_succ m n` is the proof that `m ≠ n → succ m ≠ succ n`. -/
TheoremDoc MyNat.succ_ne_succ as "succ_ne_succ" in "Peano"

/-- If $a \neq b$ then $\operatorname{succ}(a) \neq\operatorname{succ}(b)$. -/
Statement succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  Hint "Start with `contrapose! h`, to change the goal into its
  contrapositive, namely a hypothesis of `succ m = succ n` and a goal of `m = n`."
  contrapose! h
  Hint "Can you take it from here? (note: if you try `contrapose! h` again, it will
  take you back to where you started!)"
  apply succ_inj at h
  exact h
