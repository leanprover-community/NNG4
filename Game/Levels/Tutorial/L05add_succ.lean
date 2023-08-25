import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial.L03three_eq_sss0
World "Tutorial"
Level 5
Title "add_succ"

open MyNat

-- So firstly you have to say how to add `0` to something.
-- And secondly, imagine you've already said how to add `d` to something.
-- Then you have to explain how to add `succ d` to something. Once you've explained
-- those two things, \"That's it!\", or the principle of mathematical recursion,
-- says that you've defined how to add `y` to something for all natural numbers `y`.

-- So we now have two jobs to do, and let's do the simplest one in this level:

Introduction
"
We are defining addition. We have defined `x + 0` but still
need to figure out how to add successors. We need a definition for `x + succ d`,
but we are allowed to assume in our definition that we already know the
answer to `x + d`, because `d` was \"born before\" `succ d`.

Just thinking normally mathematically for a moment, `x + succ d` is one more
than `x + d`, so it's the number after `x + d`. Thus it makes sense to define
a family of hypotheses

* `add_succ (a b : ℕ) : a + succ b = succ (a + b)`

`add_succ` is a function which eats two variables and spits out a proof.
For example `add_succ 2 1` is the proof that `2 + succ 1 = succ (2 + 1)`.
The axiom tells you that you can move a `succ` left over an `+`.

`add_zero` and `add_succ` and \"That's it!\" (the principle of mathematical
recursion) now enables us to conclude that we have defined `x + y` for all
numbers `x` and `y`.

We can also now state the theorem about the successor function which has been
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
"You begin to hear dramatic music. Click next to begin the cutscene."
