import Game.Metadata
import Game.MyNat.Multiplication


World "Tutorial"
Level 2
Title "the rw tactic"

Introduction
"
In this level we make your life easier by giving you an *Assumption*. Here we have
two secret numbers $x$ and $y$, but I will also give you a hypothesis `h` stating
that `y = x + 7`. You can think about `h` as follows: `y = x + 7` is a true/false statement,
and `h` is a secret proof of this statement. It is important in games like this to distinguish
between true/false statements (which cannot be used to do anything), and theorem proofs
(which can be used to apply theorems).

The goal of this level is to prove that $2y=2(x+7)$. We want to prove this
by replacing `y` by `x + 7` and then using `rfl`. The tactic which we use to
do this kind of "substituting in" is called the *rewrite* tactic `rw`.
The tactic `rw [h]` will replace all occurences of the left hand side $y$ of `h`
in the goal, with the right hand side $x+7$.

"

Statement
"If $x$ and $y$ are natural numbers, and $y = x + 7$, then $2y = 2(x + 7)$."
    (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  Hint "You can use `rw [h]` to replace the `{y}` with `x + 7`."
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
