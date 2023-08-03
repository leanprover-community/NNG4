import Game.Metadata
import Game.MyNat.Addition


World "Tutorial"
Level 5
Title "add_zero"

open MyNat

Introduction
"
  `add_zero` is a *proof*, and it is also a *function* at the same time.

  `add_zero` is a proof of `∀ x, x + 0 = x`. In other words, it's a function
  which eats a number `x` and spits out a proof that the two numbers `x + 0` and `x` are *equal*.

  `rw` is a *tactic* which eats a list of equality proofs and then changes the goal.

  Given the goal below, clearly the way to prove it is just to cancel out all the zeros.
  So try * `rw [add_zero x]`.
"

LemmaDoc MyNat.add_succ as "add_succ" in "Add"
"One of the two axioms defining addition. It says `n + (succ m) = succ (n + m)`."

LemmaDoc MyNat.add_zero as "add_zero" in "Add"
"One of the two axioms defining addition. It says `n + 0 = n`."

Statement
"For all natural numbers $a$, we have $a + \\operatorname{succ}(0) = \\operatorname{succ}(a)$."
    : a + succ 0 = succ a := by
  Hint "You find `{a} + succ …` in the goal, so you can use `rw` and `add_succ`
  to make progress."
  Hint (hidden := true) "Explicitely, type `rw [add_succ]`!"
  rw [add_succ]
  Hint "Now you see a term of the form `… + 0`, so you can use `add_zero`."
  Hint (hidden := true) "Explicitely, type `rw [add_zero]`!"
  Branch
    simp? -- TODO
  rw [add_zero]
  Hint (hidden := true) "Finally both sides are identical."
  rfl

NewLemma MyNat.add_succ MyNat.add_zero
NewDefinition Add

Conclusion
"
You have finished tutorial world! If you're happy, let's move onto Addition World,
and learn about proof by induction.

## Inspection time

If you want to examine the proof, toggle \"Editor mode\" and click somewhere
inside the proof to see the state at that point!
"
