import Game.Metadata
import Game.MyNat.Addition


World "Tutorial"
Level 4
Title "Adding zero"

open MyNat

Introduction
"
We have defined all the numbers up to 4 (note that in this game, by \"number\"
  I *always* mean \"natural number\"), but we still cannot state
  the theorem that `2 + 2 = 4` because we have not yet defined addition.
  Let's now fix this.

# The definition of addition

Say `x` and `y` are numbers. How are we going to define `x + y`?
This is where Peano's third axiom comes in. \"That's it\" means
that if you want to define how to add `y` to something, you only have
to say how to do it in the two ways that numbers can be born.
So firstly you have to say how to add `0` to something.
And secondly, imagine you've already said how to add `d` to something.
Then you have to explain how to add `succ d` to something. Once you've explained
those two things, \"That's it!\", or the principle of mathematical recursion,
says that you've defined how to add `y` to something for all natural numbers `y`.

So we now have two jobs to do, and let's do the simplest one in this level:
let's decide how to define `x + 0`. If we want addition to agree with our intuition
we should define this to be `x`. So let's throw in a new axiom or hypothesis
or however you want to think about it, saying this:

* `add_zero (a : ℕ) : a + 0 = a`

In fact `add_zero` is a *family* of proofs. For example `add_zero 37` is a proof
that `37 + 0 = 37`, and `add_zero (p * q + r)` is a proof that `p * q + r + 0 = p * q + r`.
Mathematicians might encourage you to think of `add_zero` as just one proof:

* `add_zero : ∀ (a : ℕ), a + 0 = a`

but here it is very helpful to invoke the principle coming from computer science
(not always true, but true here) that a proof is the same as a function. Lean
is a functional programming language and you should think of `add_zero` as a function
which eats a number and spits out a proof.
"

namespace MyNat

/-- $a+(0+0)+(0+0+0)=a.$ -/
Statement (a : ℕ) : (a + (0 + 0)) + (0 + 0 + 0) = a := by
  Hint "I will walk you through this level so I can show you some
  techniques which will speed up your proving.

  This is an annoying goal. One of `rw [add_zero a]` and `rw [add_zero 0]`
  will work, but not the other. Can you figure out which? Try the one
  that works."
  Branch
    rw [add_zero 0]
    Hint "Walkthrough: Now `rw [add_zero a]` will work, so try that next."
    rw [add_zero a]
    Hint "OK this is getting old really quickly. And if we end up with more complex
    goals and have to type weird stuff like `rw [add_zero (a + 0)]` it will be
    even worse.

    Fortunately `rw` can do smart rewriting. Go back to the very start
    of this proof by clicking \"Delete\" to remove all the moves you've
    made so far and then try `rw [add_zero]` few times. Then delete all of
    these and try `repeat rw [add_zero]`.
    "
  repeat rw [add_zero]
  Hint "`rw [add_zero]` will change `? + 0` into `?`
    where `?` is arbitrary; `rw` will use the
    first solution which matches for `?`."
  rfl

LemmaDoc MyNat.add_zero as "add_zero" in "Add"
"`add_zero n` is a proof that `n + 0 = n`.

This is one of the two axioms for addition."

DefinitionDoc Add as "+" "`Add a b`, with notation `a + b`, is
the usual sum of natural numbers. Internally it is defined by
induction on one of the variables, but that is an implementation issue;
All you need to know is that `add_zero` and `zero_add` are both theorems."

NewLemma MyNat.add_zero
NewTactic «repeat» -- TODO: Do we want it to be unlocked here?
NewDefinition Add
LemmaTab "Add"

Conclusion
"
Let's now learn about Peano's second axiom for addition, `add_succ`.
"
