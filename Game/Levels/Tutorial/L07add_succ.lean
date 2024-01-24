import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial.L03two_eq_ss0

World "Tutorial"
Level 7
Title "add_succ"

TheoremTab "012"

namespace MyNat

/-- `add_succ a b` is the proof of `a + succ b = succ (a + b)`. -/
TheoremDoc MyNat.add_succ as "add_succ" in "+"

NewTheorem MyNat.add_succ

TheoremDoc MyNat.succ_eq_add_one as "succ_eq_add_one" in "+"
"`succ_eq_add_one n` is the proof that `succ n = n + 1`."

Introduction
"
Every number in Lean is either $0$ or a successor. We know how to add $0$,
but we need to figure out how to add successors. Let's say we already know
that `37 + d = q`. What should the answer to `37 + succ d` be? Well,
`succ d` is one bigger than `d`, so `37 + succ d` should be `succ q`,
the number one bigger than `q`. More generally `x + succ d` should
be `succ (x + d)`. Let's add this as a lemma.

* `add_succ x d : x + succ d = succ (x + d)`

If you ever see `... + succ ...` in your goal, `rw [add_succ]` is
normally a good idea.

Let's now prove that `succ n = n + 1`. Figure out how to get `+ succ` into
the picture, and then `rw [add_succ]`. Switch between the `+` (addition) and
`012` (numerals) tabs under \"Theorems\" on the right to
see which proofs you can rewrite.
"

/-- For all natural numbers $a$, we have $\operatorname{succ}(a) = a+1$. -/
Statement succ_eq_add_one n : succ n = n + 1 := by
  Hint "Start by unravelling the `1`."
  Hint (hidden := true) "`rw [one_eq_succ_zero]` will do this."
  rw [one_eq_succ_zero]
  Hint (hidden := true) "Now you can `rw [add_succ]`"
  rw [add_succ]
  Hint (hidden := true) "And now `rw [add_zero]`"
  rw [add_zero]
  Hint (hidden := true) "And finally `rfl`."
  rfl

Conclusion
"[dramatic music]. Now are you ready to face the first boss of the game?"
