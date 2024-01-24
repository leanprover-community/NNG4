import Game.Levels.AdvMultiplication.L02mul_left_ne_zero

World "AdvMultiplication"
Level 3
Title "eq_succ_of_ne_zero"

TheoremTab "≤"

namespace MyNat

TacticDoc tauto "
# Summary

The `tauto` tactic will solve any goal which can be solved purely by logic (that is, by
truth tables).

## Example

If you have `False` as a hypothesis, then `tauto` will solve
the goal. This is because a false hypothesis implies any hypothesis.

## Example

If your goal is `True`, then `tauto` will solve the goal.

## Example

If you have two hypotheses `h1 : a = 37` and `h2 : a ≠ 37` then `tauto` will
solve the goal because it can prove `False` from your hypotheses, and thus
prove the goal (as `False` implies anything).

## Example

If you have one hypothesis `h : a ≠ a` then `tauto` will solve the goal because
`tauto` is smart enough to know that `a = a` is true, which gives the contradiction we seek.

## Example

If you have a hypothesis of the form `a = 0 → a * b = 0` and your goal is `a * b ≠ 0 → a ≠ 0`, then
`tauto` will solve the goal, because the goal is logically equivalent to the hypothesis.
If you switch the goal and hypothesis in this example, `tauto` would solve it too.
"

NewTactic tauto

TheoremDoc MyNat.eq_succ_of_ne_zero as "eq_succ_of_ne_zero" in "≤" "
`eq_succ_of_ne_zero a` is a proof that `a ≠ 0 → ∃ n, a = succ n`.
"

Introduction
"Multiplication usually makes a number bigger, but multiplication by zero can make
it smaller. Thus many lemmas about inequalities and multiplication need the
hypothesis `a ≠ 0`. Here is a key lemma enables us to use this hypothesis.
To help us with the proof, we can use the `tauto` tactic. Click on the tactic's name
on the right to see what it does.
"

Statement eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  Hint "Start with `cases a with d` to do a case split on `a = 0` and `a = succ d`."
  cases a with d
  · Hint "In the \"base case\" we have a hypothesis `ha : 0 ≠ 0`, and you can deduce anything
  from a false statement. The `tauto` tactic will close this goal."
    tauto
  · use d
    rfl
