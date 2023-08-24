import Game.Metadata
import Game.MyNat.Multiplication


World "Tutorial"
Level 2
Title "the rw tactic"

Introduction
"
In this level we make your life easier by giving you an *Assumption*. Here we have
two secret numbers $x$ and $y$, but I will also give you a hypothesis `h` stating
that `y = x + 7`. You can see `h` listed in your Assumptions just above the
statment of the goal.

You can think about `h` as follows: `y = x + 7` is a true/false statement,
and `h` is a secret proof of this statement. It is important in games like this
to have a clear separation in your mind about the difference between the
*statement* of a theorem and its *proof*. Here, for example, the statement
is `y = x + 7` and the proof is `h`.

The goal of this level is to prove that $2y=2(x+7)$. We want to prove this
by replacing `y` by `x + 7` and then using `rfl`. The tactic which we use to
do this kind of \"substituting in\" is called the *rewrite* tactic `rw`.
The tactic `rw [h]` will replace all occurences of the left hand side $y$ of `h`
in the goal, with the right hand side $x+7$. Try it and see.
"

/-- If $x$ and $y$ are natural numbers, and $y = x + 7$, then $2y = 2(x + 7)$. -/
Statement
    (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  Hint "You can use `rw [h]` to replace the `{y}` with `x + 7`."
  rw [h]
  Hint "Not all hints are directly shown. If you are stuck and need more help
  finishing the proof, click on \"Show more help!\" below."
  Hint (hidden := true)
  "Now both sides are identical, so you can use `rfl` to close the goal."
  rfl

TacticDoc rw "
## Summary

If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s. Variants: `rw ← h` (changes
`Y` to `X`) and
`rw h at h2` (changes `X` to `Y` in hypothesis `h2` instead
of the goal).

## Details

The `rw` tactic is a way to do \"substituting in\". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw h`
will change them all to `B`'s.

2) The `rw` tactic will also work with proofs of theorems
which are equalities (look for them in the drop down
menu on the left, within Theorem Statements).
For example, in world 1 level 4
we learn about `add_zero x : x + 0 = x`, and `rw add_zero`
will change `x + 0` into `x` in your goal (or fail with
an error if Lean cannot find `x + 0` in the goal).

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw h` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\\l` and
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:
```
x y : mynat
h : x = y + y
⊢ succ (x + 0) = succ (y + y)
```

then

`rw add_zero,`

will change the goal into `⊢ succ x = succ (y + y)`, and then

`rw h,`

will change the goal into `⊢ succ (y + y) = succ (y + y)`, which
can be solved with `refl,`.

### Example:
You can use `rw` to change a hypothesis as well.
For example, if your local context looks like this:
```
x y : mynat
h1 : x = y + 3
h2 : 2 * y = x
⊢ y = 3
```
then `rw h1 at h2` will turn `h2` into `h2 : 2 * y = y + 3`.
-/
"

NewTactic rw

Conclusion
"
If you want to inspect the proof you created, toggle \"Editor mode\" by clicking
on the `</>` button in the top right. In editor mode,
you can click around the proof and see the state of Lean's brain at any point.
If you want to go back to interactive mode with hints, click the button again.

In editor mode, note that each tactic is written on a new line and Lean is sensitive
to indentation (i.e. there must be no spaces before any of the tactics).
"
