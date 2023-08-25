import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial.L03three_eq_sss0
World "Tutorial"
Level 5
Title "add_succ"

open MyNat

Introduction
"
Our remaining job if we want to cover all cases of addition,
is defining `x + succ d`, assuming that we already know the answer to `x + d`.
Clearly `x + succ d` is one more than `x + d`, so it's the number after `x + d`.
Thus it makes sense to define a family of hypotheses

* `add_succ (a b : ℕ) : a + succ b = succ (a + b)`

This axiom tells you that you can move a `succ` left over an `+`.

We can now state the theorem about the successor function which has been
part of our mental model: `succ n = n + 1`. See if you can rewrite your
way to a proof of it.
"
namespace MyNat

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


LemmaDoc MyNat.succ_eq_add_one as "succ_eq_add_one" in "Add"
"`succ_eq_add_one n` is the proof that `succ n = n + 1`."

NewLemma MyNat.add_succ MyNat.succ_eq_add_one
LemmaTab "Add"


Conclusion
"You begin to hear boss music. Click next to begin the cutscene."
