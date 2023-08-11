import Game.Metadata
import Game.MyNat.Addition


World "Tutorial"
Level 6
Title "add_succ"

open MyNat

Introduction
"
Peano's second axiom was this:

* `add_succ : ∀ (a b : ℕ), a + succ b = succ (a + b)`

It tells you that you can move a `succ` left over an `+`. See if you can rewrite
your way to a proof of this.
"
namespace MyNat

/-- For all natural numbers $a$, we have $a + \operatorname{succ}(0) = \operatorname{succ}(a)$. -/
Statement : a + succ 0 = succ a := by
  Hint "You find `{a} + succ …` in the goal, so you can use `rw` and `add_succ`
  to make progress."
  Hint (hidden := true) "Explicitely, you can type `rw [add_succ a 0]`
  if you want to be precise, or just `rw [add_succ]` if you want Lean to figure
  out the inputs to this function."
  rw [add_succ]
  Branch
    simp?
  Hint (hidden := true) "Now you see a term of the form `… + 0`, so you can use `add_zero`."
  rw [add_zero]
  Hint (hidden := true) "Finally both sides are identical."
  rfl


LemmaDoc MyNat.add_succ as "add_succ" in "Add"
"`add_succ a b` is the proof of `a + succ b = succ (a + b)`."

NewLemma MyNat.add_succ
LemmaTab "Add"

Conclusion
"
You have finished tutorial world! If you're happy, let's move onto Addition World,
and learn about proof by induction.

## Inspection time

If you want to examine your proofs, toggle \"Editor mode\" and click somewhere
inside the proof to see the state of Lean's brain at that point.
"
