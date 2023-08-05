import Game.Metadata
import Game.MyNat.Addition


World "Tutorial"
Level 5
Title "addition"

open MyNat

Introduction
"
Peano defined addition $a + b$ by adding two axioms to his system.
Peano's first axiom was called `add_zero`. Here it is:

* `add_zero : ∀ (a : ℕ), a + 0 = a`

In words, the theorem says that if `a` is an arbitrary natural number, then `a + 0 = a`.
Another way to think of `add_zero` is as a function, which eats a natural number `a`
and returns a proof `add_zero a` of `a + 0 = a`.

Let me show you how to use Lean's simplifier `simp`
to do a lot of work for us."

LemmaDoc MyNat.add_zero as "add_zero" in "Add"
"One of the two axioms defining addition. It says `n + 0 = n`."

namespace MyNat

TacticDoc simp "The simplifier. `rw` on steroids.

A bunch of lemmas like `add_zero : ∀ a, a + 0 = a`
are tagged with the `@[simp]` tag. If the `simp` tactic
is run by the user, the simplifier will try and rewrite
as many of the lemmas tagged `@[simp]` as it can.

`simp` is a *finishing tactic*. After you run `simp`,
the goal should be closed. If it is not, it is best
practice to write `simp?` instead and then replace the
output with the appropriate `simp only` call. Inappropriate
use of `simp` can make for very slow code.
"
NewTactic simp -- TODO: Do we want it to be unlocked here?

Statement
"$(a+(0+0)+(0+0+0)=a.$"
  (a : ℕ)  : (a + (0 + 0)) + (0 + 0 + 0) = a := by
  Hint "I want this to say \"Walkthrough\".

  This is an annoying goal. One of rw [add_zero a]` amd `rw [add_zero 0]`
  will work, but not the other. Can you figure out which? Try the one
  that works."
  Branch
    rw [add_zero 0]
    Hint "Walkthrough: Now `rw [add_zero a]` will work, so try that next."
    rw [add_zero a]
    Hint "OK this is getting old really quickly. And if we have to type
    weird stuff like `rw [add_zero (a + 0)]` it will be even worse.
    Fortunately `rw` can do smart rewriting. Go back to the very start
    of this proof with \"undo\" and try `repeat rw [add_zero]`
    "
  Branch
    repeat rw [add_zero]
    Hint "`rw` can rewrite proofs of the form `? + 0 = ?`
    where `?` is arbitrary, and it will just use the
    first solution which matches for `?`.

    The rest of he proof is easy, but don't finish yet, there's more.

    Lean's simplifier is a tool which does repeated
    rewriting. And `add_zero` is a `simp` lemma. So go back to the
    start again and just try `simp`."
  simp

NewLemma MyNat.add_zero

DefinitionDoc Add as "Add" "`Add a b`, with notation `a + b`, is
the usual sum of natural numbers. Internally it is defined by
induction on one of the variables, but that is an implementation issue;
All you need to know is that `add_zero` and `zero_add` are both theorems."

NewDefinition Add

Conclusion
"
  The simplifier atempts to solve goals by using *repeated rewriting* of
  *equalities* and *iff statements*, and then trying `rfl` at the end.

  Let's now learn about Peano's second axiom for addition, `add_succ`.
"
