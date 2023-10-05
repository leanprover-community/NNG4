import Game.Levels.Addition
import Game.MyNat.AdvAddition

World "AdvAddition"
Level 6
Title "intro"

namespace MyNat

Introduction
" We have seen how to `apply` theorems and assumptions of
of the form `P → Q`. But what if our *goal* is of the form `P → Q`?
We need to know how to say \"let's assume `P`\" in Lean.
We do this with the `intro` tactic, the last tactic you need
to learn to solve all the levels in this world.
"

/-- $x=37\\implies x=37$. -/
Statement (x : ℕ) : x = 37 → x = 37 := by
  Hint "Start with `intro h` to assume the hypothesis."
  intro h
  Hint (hidden := true) "Now `assumption` finishes the job."
  assumption
