import Game.Levels.AdvMultiplication.L05le_one

World "AdvMultiplication"
Level 6
Title "mul_right_eq_one"

LemmaTab "*"

namespace MyNat

TacticDoc «have» "
# Summary

The `have` tactic can be used to add new hypotheses to a level, but of course
you have to prove them.


## Example

The simplest usage is like this. If you have `a` in your context and you execute

`have ha : a = 0`

then you will get a new goal `a = 0` to prove, and after you've proved
it you will have a new hypothesis `ha : a = 0` in your original goal.

## Example

If you already have a proof of what you want to `have`, you
can just create it immediately. For example, if you have `a` and `b`
number objects, then

`have h2 : succ a = succ b → a = b := succ_inj a b`

will directly add a new hypothesis `h2 : succ a = succ b → a = b`
to the context, because you just supplied the proof of it (`succ_inj a b`).

## Example

If you have a proof to hand, then you don't even need to state what you
are proving. example

`have h2 := succ_inj a b`

will add `h2 : succ a = succ b → a = b` as a hypothesis.
"

NewTactic «have»

LemmaDoc MyNat.mul_right_eq_one as "mul_right_eq_one" in "*" "
`mul_right_eq_one a b` is a proof that `a * b = 1 → a = 1`.
"

Introduction
"
This is the multiplicative analogue of Advanced Addition World's `x + y = 0 → x = 0`.
We'll prove it using a new tactic called `have`.
"

Statement mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  Hint "We want to use `le_mul_right`, but we need a hypothesis `x * y ≠ 0`
  which we don't have. Yet. Try `have h2 : x * y ≠ 0`. You'll be asked to
  prove it, and then you'll have a new hypothesis which you can apply
  `le_mul_right` to."
  have hx : x * y ≠ 0
  rw [h, one_eq_succ_zero]
  symm
  apply zero_ne_succ
  Hint (hidden := true) "Now you can `apply le_mul_right at hx`."
  apply le_mul_right at hx
  Hint (hidden := true) "Now `rw [h] at hx` so you can `apply le_one at hx`."
  rw [h] at hx
  apply le_one at hx
  Hint (hidden := true) "Now `cases hx with h0 h1` and deal with the two
  cases separately."
  cases hx with h0 h1
  · rw [h0, zero_mul] at h
    apply zero_ne_succ at h
    tauto
  exact h1
