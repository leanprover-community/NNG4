import Game.Metadata
import Game.MyNat.Multiplication


World "Tutorial"
Level 2
Title "the rw tactic"

Introduction
"
In this level we make your life easier by giving you an *Assumption*. Here we have
two secret numbers $x$ and $y$, but I will also give you a hypothesis `h` stating
that `y = x + 7`. You can think of `y = x + 7` as being the statement of a theorem,
and `h` being its secret proof.

`h` is the proof of an equality, and the *rewrite* tactic `rw` consumes lists
of equality proofs. Rewriting is the way that we \"substitute in\" the value of
a variable. Let's see the rewrite tactic in action.
"

Statement
"If $x$ and $y$ are natural numbers, and $y = x + 7$, then $2y = 2(x + 7)$."
    (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  Hint "You can use `rw [h]` to replace the `{y}` with `x + 7`."
--  Note that the assumption `h` is written
--  inside square brackets: `[h]`."
  rw [h]
  Hint "Not all hints are directly shown. If you are stuck and need more help
  finishing the proof, click on \"More Help\" below!"
  Hint (hidden := true)
  "Now both sides are identical, so you can use `rfl` to close the goal."
  rfl

NewTactic rw

Conclusion
"
If you want to inspect the proof you created, toggle \"Editor mode\" above. In editor mode,
you can click around the proof and see the state of Lean's brain at any point.

Each tactic is written on a new line and Lean is sensitive to indentation (i.e. there must be no
spaces before any of the tactics).
"
