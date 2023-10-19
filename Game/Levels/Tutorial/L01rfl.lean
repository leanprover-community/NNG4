import Game.Metadata
import Game.MyNat.Multiplication


World "Tutorial"
Level 1
Title "The rfl tactic"

Introduction
"
# Read this first

Each level in this game involves proving a mathematical theorem (the \"Goal\").
The goal will be a statement about *numbers*. Some numbers in this game have known values.
Those numbers have names like $37$. Other numbers will be secret. They're called things
like $x$ and $q$. We know $x$ is a number, we just don't know which one.

In this first level we're going to prove the theorem that $37x + q = 37x + q$.
You can see `x q : ℕ` in the *Objects* below, which means that `x` and `q`
are numbers.

We solve goals in Lean using *Tactics*, and the first tactic we're
going to learn is called `rfl`, which proves all theorems of the form $X = X$.

Prove that $37x+q=37x+q$ by casting the `rfl` tactic.
"

/-- If $x$ and $q$ are arbitrary natural numbers, then $37x+q=37x+q.$ -/
Statement (x q : ℕ) : 37 * x + q = 37 * x + q := by
  Hint "In order to use the tactic `rfl` you can enter it in the text box
  under the goal and hit \"Execute\"."
  rfl

TacticDoc rfl
"
## Summary

`rfl` proves goals of the form `X = X`.

In other words, the `rfl` tactic will close any goal of the
form `A = B` if `A` and `B` are *identical*.

`rfl` is short for \"reflexivity (of equality)\".

## Example:

If the goal looks like this:

```
x + 37 = x + 37
```

then `rfl` will close it. But if it looks like `0 + x = x` then `rfl` won't work, because even
though $0+x$ and $x$ are always equal as *numbers*, they are not equal as *terms*.
The only term which is identical to `0 + x` is `0 + x`.

## Details

`rfl` is short for \"reflexivity of equality\".

## Game Implementation

*Note that our `rfl` is weaker than the version used in core Lean and `mathlib`,
for pedagogical purposes; mathematicians do not distinguish between propositional
and definitional equality because they think about definitions in a different way
to type theorists (`zero_add` and `add_zero` are both \"facts\" as far
as mathematicians are concerned, and who cares what the definition of addition is).*
"

NewTactic rfl

Conclusion
"
Congratulations! You completed your first verified proof!

Remember that `rfl` is a *tactic*. If you ever want information about the `rfl` tactic,
you can click on `rfl` in the list of tactics on the right.

Now click on \"Next\" to learn about the `rw` tactic.
"
