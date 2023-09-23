import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial.L03three_eq_sss0
World "Tutorial"
Level 5
Title "add_succ"

open MyNat

Introduction
"
We need to figure out how to add successors. Let's say we know the
answer to `x + d`. What should the answer to `x + succ d` be? Well,
`succ d` is one bigger than `d`, so `x + succ d` should be one bigger
than `x + d`.

* `add_succ x d : x + succ d = succ (x + d)`

If you ever see `... + succ ...` in your goal, `rw [add_succ]` should
make progress.

Let's now prove that `succ n = n + 1`. Use the Add and Numeral tabs to
switch between lemmas so you can see what you can rewrite.
"
namespace MyNat

LemmaDoc MyNat.succ_eq_add_one as "succ_eq_add_one" in "Add"
"`succ_eq_add_one n` is the proof that `succ n = n + 1`."

/-- For all natural numbers $a$, we have $\operatorname{succ}(a) = a+1$. -/
Statement succ_eq_add_one n : succ n = n + 1 := by
  Hint (hidden := true) "First unravel the `1`."
  rw [one_eq_succ_zero]
  Hint (hidden := true) "Now you can `rw [add_succ]`"
  rw [add_succ]
  rw [add_zero]
  rfl

LemmaDoc MyNat.add_succ as "add_succ" in "Add"
"`add_succ a b` is the proof of `a + succ b = succ (a + b)`."


NewLemma MyNat.add_succ MyNat.succ_eq_add_one
LemmaTab "Add"

Conclusion
"[dramatic music]. Now are you ready to face the boss?"
