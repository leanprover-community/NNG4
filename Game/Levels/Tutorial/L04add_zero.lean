import Game.Metadata
import Game.MyNat.Addition


World "Tutorial"
Level 4
Title "Adding zero"

open MyNat

Introduction
"
We have defined all the numbers up to 4, but we still cannot *state*
  the theorem that `2 + 2 = 4` because we haven't yet defined addition.
  Before we do this, we need to informally introduce the final axiom
  used in this game.

# \"There's only two ways to make numbers\"

  Peano's third axiom, informally, says that `0` and `succ` are *the
  only ways to make numbers*. More precisely: if we want to do something
  for *every number*, then all we have to do is two things:

  * Do it for `0`.

  * Assuming we've done it for `n`, do it for `succ n`.

  The axiom then guarantees that we've done it for all numbers.

# The definition of addition

Let's try and define the function which adds `37` to a number, using
this principle. We have to do two things.

* We must define `37 + 0`.

* If we already know what `37 + n` is, we must define `37 + succ n`.

# Adding 0

To make addition agree with our intuition, we should define `37 + 0`
to be `37`. More generally, we should define `x + 0` to be `x` for
any number `x`. The name of this hypothesis in Lean is `add_zero x`.

`add_zero 37 : 37 + 0 = 37`

`add_zero x : x + 0 = x`

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

Conclusion "Those of you interested in speedrunning the game may want to know
that `repeat rw [add_zero]` will do both rewrites at once."



DefinitionDoc Add as "+" "`Add a b`, with notation `a + b`, is
the usual sum of natural numbers. Internally it is defined by
recursion on b, with the two \"equation lemmas\" being

* `add_zero a : a + 0 = a`

* `add_succ a b : a + succ b = succ (a + b)

Other theorems about naturals, such as `zero_add a : 0 + a = a`, are proved
by induction from these two basic theorems."

NewDefinition Add

LemmaTab "Add"

LemmaDoc MyNat.add_zero as "add_zero" in "Add"
"`add_zero n` is a proof that `n + 0 = n`.

You can think of `add_zero` as a function, which
eats a number, and returns a proof of a theorem
about that number. For example `add_zero 37` is
a proof that `37 + 0 = 37`.

A mathematician sometimes thinks of `add_zero`
as \"one thing\", namely a proof of $\\forall n ∈ ℕ, n + 0 = n$$`."

NewLemma MyNat.add_zero

TacticDoc «repeat» "
## Summary

`repeat t` repeatedly applies the tactic `t`
to the goal.

## Example

`repeat rw [add_zero]` will turn the goal
`⊢ a + 0 + (0 + (0 + 0)) = b + 0 + 0`
into the goal
`⊢ a = b`

## Variant

`repeat' t` applies `t` to all subgoals
more reliably.
"
NewTactic «repeat» -- TODO: Do we want it to be unlocked here?

Conclusion
"
Let's now learn about Peano's second axiom for addition, `add_succ`.
"
