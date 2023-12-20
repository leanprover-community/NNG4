import Game.Levels.AdvAddition.L05add_right_eq_self
import Game.Tactic.Cases

World "AdvAddition"
Level 6
Title "eq_zero_of_add_right_eq_zero"

LemmaTab "Peano"

namespace MyNat

Introduction
"The next result we'll need in Less or Equal World is that if `a + b = 0` then `a = 0` and `b = 0`.
Let's prove one of these facts in this level, and the other in the next.

## A new tactic: `cases`

The `cases` tactic will split an object or hypothesis up into the possible ways
that it could have been created.

For example, sometimes you want to deal with the two cases `b = 0` and `b = succ d` separately,
but don't need the inductive hypothesis `hd` that comes with `induction b with d hd`.
In this situation you can use `cases b with d` instead. There are two ways to make
a number: it's either zero or a successor. So you will end up with two goals, one
with `b = 0` and one with `b = succ d`.

Another example: if you have a hypothesis `h : False` then you are done, because a false statement implies
any statement. Here `cases h` will close the goal, because there are *no* ways to
make a proof of `False`! So you will end up with no goals, meaning you have proved everything.

"

TacticDoc cases "
## Summary

If `n` is a number, then `cases n with d` will break the goal into two goals,
one with `n = 0` and the other with `n = succ d`.

If `h` is a proof (for example a hypothesis), then `cases h with...` will break the
proof up into the pieces used to prove it.

## Example

If `n : ℕ` is a number, then `cases n with d` will break the goal into two goals,
one with `n` replaced by 0 and the other with `n` replaced by `succ d`. This
corresponds to the mathematical idea that every natural number is either `0`
or a successor.

## Example

If `h : P ∨ Q` is a hypothesis, then `cases h with hp hq` will turn one goal
into two goals, one with a hypothesis `hp : P` and the other with a
hypothesis `hq : Q`.

## Example

If `h : False` is a hypothesis, then `cases h` will turn one goal into no goals,
because there are no ways to make a proof of `False`! And if you have no goals left,
you have finished the level.

## Example

If `h : a ≤ b` is a hypothesis, then `cases h with c hc` will create a new number `c`
and a proof `hc : b = a + c`. This is because the *definition* of `a ≤ b` is
`∃ c, b = a + c`.
"
NewTactic cases

LemmaDoc MyNat.eq_zero_of_add_right_eq_zero as "eq_zero_of_add_right_eq_zero" in "+" "
  A proof that $a+b=0 \\implies a=0$.
"

-- **TODO** why `add_eq_zero_right` and not `add_right_eq_zero`?
-- https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/eq_zero_of_add_eq_zero_right/near/395716874

/-- If $a+b=0$ then $a=0$. -/
Statement eq_zero_of_add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  Hint "Here we want to deal with the cases `b = 0` and `b ≠ 0` separately,
  so start with `cases b with d`."
  cases b with d
  intro h
  rw [add_zero] at h
  exact h
  intro h
  rw [add_succ] at h
  symm at h
  apply zero_ne_succ at h
  cases h

Conclusion "Well done!"
