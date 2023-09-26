import Game.Metadata
import Game.MyNat.Addition


World "Tutorial"
Level 4
Title "Adding zero"

Introduction
"
We'd like to prove `2 + 2 = 4` but right now
we can't even *state* it
because we haven't yet defined addition.

## Defining addition.

How are we going to add $37$ to an arbitrary number $x$? Well,
there are only two ways to make numbers in this game: $0$
and successors. So to define `37 + x` we will need
to know what `37 + 0` is and what `37 + succ x` is.
Let's start with adding `0`.

### Adding 0

To make addition agree with our intuition, we should *define* `37 + 0`
to be `37`. More generally, we should define `a + 0` to be `a` for
any number `a`. The name of this hypothesis in Lean is `add_zero a`.

* `add_zero 37 : 37 + 0 = 37`

* `add_zero a : a + 0 = a`

You can think of `add_zero` as a function which eats a number, and spits
out a proof about that number.
"

namespace MyNat

/-- $a+(b+0)+(c+0)=a+b+c.$ -/
Statement (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  Hint "`rw [add_zero b]` will change `b + 0` into `b`."
  repeat rw [add_zero b]
  Hint "`rw [add_zero]` will change `? + 0` into `?` for the first value of `?` which works."
  rw [add_zero]
  rfl

DefinitionDoc Add as "+" "`Add a b`, with notation `a + b`, is
the usual sum of natural numbers. Internally it is defined
via the following two hypotheses:

* `add_zero a : a + 0 = a`

* `add_succ a b : a + succ b = succ (a + b)`

Other theorems about naturals, such as `zero_add a : 0 + a = a`, are proved
by induction using these two basic theorems."

NewDefinition Add

LemmaTab "Add"

LemmaDoc MyNat.add_zero as "add_zero" in "Add"
"`add_zero a` is a proof that `a + 0 = a`.

You can think of `add_zero` as a function, which
eats a number, and returns a proof of a theorem
about that number. For example `add_zero 37` is
a proof that `37 + 0 = 37`.

A mathematician sometimes thinks of `add_zero`
as \"one thing\", namely a proof of $\\forall n ∈ ℕ, n + 0 = n$.
This is just a different way of thinking about the same concept."

NewLemma MyNat.add_zero

TacticDoc «repeat» "
## Summary

`repeat t` repeatedly applies the tactic `t`
to the goal. You don't need to use this
tactic, it just speeds things up sometimes.

## Example

`repeat rw [add_zero]` will turn the goal
`a + 0 + (0 + (0 + 0)) = b + 0 + 0`
into the goal
`a = b`.

## Example

If the goal contains `a + b`, then
`repeat rw [add_comm]` will make Lean hang,
because it will swap `a + b` to `b + a`
and back all day long.

**TODO** check this

**TODO** hide `repeat` tactic from the user.
"
NewTactic «repeat»

Conclusion "Those of you interested in speedrunning the game may want to know
that `repeat rw [add_zero]` will do both rewrites at once.

Let's now learn about Peano's second axiom for addition, `add_succ`.
"
