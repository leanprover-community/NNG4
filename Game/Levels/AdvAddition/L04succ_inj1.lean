import Game.Levels.Addition
import Game.MyNat.AdvAddition

World "AdvAddition"
Level 4
Title "succ_inj : the successor function is injective"

namespace MyNat

LemmaTab "Peano"

Introduction
"
If `a` and `b` are numbers, then `succ_inj a b` is a proof
that `succ a = succ b` implies `a = b`. Click on this theorem in the *Peano*
tab for more information.

Peano had this theorem as an axiom, but in Functional Programming World
we will show how to prove it. Right now let's just assume it,
and let's solve an equation using it. We will solve the equation
by manipulating our hypothesis until it becomes the goal.
"

LemmaDoc MyNat.succ_inj as "succ_inj" in "Peano" "

# Statement

If $a$ and $b$ are numbers, then
`succ_inj a b` is the proof that
$ (\\operatorname{succ}(a) = \\operatorname{succ}(b))\\implies a=b$.

## More technical details

There are other ways to think about `succ_inj`.

You can think about `succ_inj` itself as a function which takes two
numbers $$a$$ and $$b$$ as input, and outputs a proof of
$ (\\operatorname{succ}(a) = \\operatorname{succ}(b))\\implies a=b$.

You can think of `succ_inj` itself as a proof; it is the proof
that `succ` is an injective function. In other words,
`succ_inj` is a proof of
$\\forall a b\\in \\mathbb{N}, (\\operatorname{succ}(a) = \\operatorname{succ}(b))\\implies a=b$.

`succ_inj` was postulated as an axiom by Peano, but
in Lean it can be proved using `pred`, a mathematically
pathological function.
"

NewLemma MyNat.succ_inj

/-- If $x+1=4$ then $x=3$. -/
Statement (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  Hint "Let's first get `h` into the form `succ x = succ 3.` so we can
  apply `succ_inj`. First rewrite
  `four_eq_succ_three` at `h` to change the 4 on the right hand side."
  rw [four_eq_succ_three] at h
  Hint "Now rewrite `succ_eq_add_one` backwards at `h`
  to get the right hand side."
  Hint (hidden := true) "`rw [← succ_eq_add_one] at h`. Look at the
  docs for `rw` for an explanation. Type `←` with `\\l`."
  rw [←succ_eq_add_one] at h
  Hint "Now let's `apply` our new theorem. Cast `apply succ_inj at h`
  to change `h` to a proof of `x = 3`."
  apply succ_inj at h
  Hint "Now finish in one line."
  Hint (hidden := true) "And now we've deduced what we wanted to prove: the goal is one of our assumptions.
  Finish the level with `assumption`."
  assumption

Conclusion "In the next level, we'll do the same proof but backwards."
