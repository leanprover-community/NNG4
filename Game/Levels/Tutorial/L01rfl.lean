import Game.Metadata
import Game.MyNat.Multiplication


World "Tutorial"
Level 1
Title "The rfl tactic"

Introduction
"
Each level in this game involves proving a mathematical theorem (the \"Goal\").
In this first level we're going to learn how to prove the theorem that $37x + q = 37x + q$.
Here $x$ and $q$ are secret numbers (you can see them listed under \"Objects\"))
and $37$ is a non-secret number.

We prove theorems using *Tactics*, and the first tactic we're
going to learn is called `rfl`, which is short for \"reflexivity of equality\",
an intimidating way of saying that $X = X$ is always true.

Prove that $37x+q=37x+q$ by casting the `rfl` tactic.
"

Statement
"If $x$ and $q$ are arbitrary natural numbers, then $37x+q=37x+q.$"
    (x q : ℕ) : 37 * x + q = 37 * x + q := by
  Hint "In order to use the tactic `rfl` you can enter it above and hit \"Execute\"."
  rfl

TacticDoc rfl "
## Summary

`rfl` proves goals of the form `X = X`.

## Details

The `rfl` tactic will close any goal of the form `A = B` if `A` and `B` are
*exactly the same thing*.

## Example:

If the goal looks like this:

```
⊢ x^37+691*y^24+1=x^37+691*y^24+1
```

then `rfl` will close it. But if it looks like `0 + x = x` then `rfl` won't work, because even though $0+x$ is *equal* to $x$, it is not *exactly the same thing* as *x*. The only thing which is exactly the same as `0 + x` is `0 + x`.
"
NewTactic rfl
DefinitionDoc MyNat as "Nat" "The natural numbers, defined as an inductive type, with two constructors:

* `0 : Nat`
* `succ (n : Nat) : Nat`
"
NewDefinition MyNat

Conclusion
"
Congratulations! You completed your first verified proof!

Most of the levels in this game aren't as easy as that one. One thing it is important to
learn about `rfl` is that it will *not* prove theorems such as `x + y = y + x`. We all
*know* that `x + y = y + x`, but `rfl` doesn't work like that. `rfl` will prove a theorem
of the form `X = Y` if `X` and `Y` are *syntactically equal*, i.e. made by pressing
the same buttons on your keyboard in the same order.


If you want to be reminded about the `rfl` tactic, your inventory on the right contains useful
information about things you've learned.

Now click on \"Next\" to continue the journey.
"
