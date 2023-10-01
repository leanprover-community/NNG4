import Game.Levels.Addition
import Game.MyNat.AdvAddition

World "AdvAddition"
Level 1
Title "succ_inj : an implication"

namespace MyNat

LemmaTab "succ"

TacticDoc apply "
## Summary

If `t : P → Q` is a proof that $P\\implies Q$, and `h : P` is a proof of `P`,
then `apply t at h` will change `h` to a proof of `Q`.

If the goal is `Q`, then `apply t` will \"argue backwards\" and change the
goal to `P`.

### Example:

If you have a hypothesis `h : succ (a + 37) = succ (b + 42)`
then `apply succ_inj at h` will change `h` to `a + 37 = b + 42`.

### Example

If the goal is `a * b = 7`, then `apply succ_inj` will turn the
goal into `succ (a * b) = succ 7`
"
NewTactic apply

TacticDoc assumption "
## Summary

This tactic closes the goal if the goal is *identically* one
of the assumptions.

### Example

If the goal is `x = 37` and you have a hypothesis `main_result_2 : x = 37`
then `assumption` will solve the goal.
"

NewTactic assumption


Introduction
"
If `a` and `b` are numbers, then `succ_inj a b` is a proof
that `succ a = succ b` implies `a = b`.

This is one of Peano's axioms. Let's see how to use it
with the `apply` tactic.
"

LemmaDoc MyNat.succ_inj as "succ_inj" in "succ" "

# Statement

If $a$ and $b$ are numbers, then
`succ_inj a b` is the proof that
$ (\\operatorname{succ}(a) = \\operatorname{succ}(b))\\implies a=b$.

## More technical details

You can think of `succ_inj` itself as being a proof
that `succ` is an injective function. In other words,
`succ_inj : ∀ (a b : ℕ), succ a = succ b → a = b`
You can eliminate the `∀`s by supplying inputs to
the function.

`succ_inj` was postulated as an axiom by Peano, but
in Lean it can be proved using `pred`, a mathematically
pathological function. **TODO** does the kernel prove
this at some point? Same question for succ_ne_zero.
"

NewLemma MyNat.succ_inj

/-- If $x+1=4$ then $x=3$. -/
Statement (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  Hint "Let's first get `h` into the form `succ x = succ 3.` First rewrite `four_eq_succ_three`
  at `h` to change the 4 on the right hand side."
  rw [four_eq_succ_three] at h
  Hint "Remember `succ_eq_add_one`? Rewrite it backwards at `h`
  to get the right hand side. Look at
  the docs for `rw` if you don't know how to do this."
  rw [←succ_eq_add_one] at h
  Hint "Now take a look at the documentation for `succ_inj`, in the **TODO** what tab? tab.
  Let's `apply` that theorem. Cast `apply succ_inj at h`."
  apply succ_inj at h
  Hint "And now we've deduced what we wanted to prove: the goal is one of our assumptions.
  Finish the level with `assumption`."
  assumption

Conclusion "In the next level, we'll do the same proof but backwards."
