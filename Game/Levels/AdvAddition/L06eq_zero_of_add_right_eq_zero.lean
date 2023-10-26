import Game.Levels.AdvAddition.L05add_right_eq_self
import Game.Tactic.Cases

World "AdvAddition"
Level 6
Title "eq_zero_of_add_right_eq_zero"

LemmaTab "Peano"

namespace MyNat

Introduction
" We have still not proved that if `a + b = 0` then `a = 0` and also `b = 0`. Let's finish this
world by proving one of these in this level, and the other in the next.

## Two new tactics

If you have a hypothesis `h : False` then you are done, because a false statement implies
any statement. You can use the `tauto` tactic to finish your proof.

Sometimes you just want to deal with the two cases `b = 0` and `b = succ d` separately,
and don't need the inductive hypothesis `hd` that comes with `induction b with d hd`.
In this situation you can use `cases b with d` instead.

"

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

If you have a hypothesis of the form `a = 0 → a * b = 0` and your goal is `a * b ≠ 0 → a ≠ 0`, then
`tauto` will solve the goal, because the goal is logically equivalent to the hypothesis.
If you switch the goal and hypothesis in this example, `tauto` would solve it too.
"

TacticDoc cases "
## Summary

If `n` is a number, then `cases n with d` will break the goal into two goals,
one with `n = 0` and the other with `n = succ d`.

If `h` is a proof (for example a hypothesis), then `cases h with...` will break the
proof up into the pieces used to prove it.

## Example

If `h : a ≤ b` is a hypothesis, then `cases h with c hc` will create a new number `c`
and a proof `hc : b = a + c`. This is because the *definition* of `a ≤ b` is
`∃ c, b = a + c`.

## Example

If `n : ℕ` is a number, then `cases n with d` will break the goal into two goals,
one with `n` replaced by 0 and the other with `n` replaced by `succ d`. This
corresponds to the mathematical idea that every natural number is either `0`
or a successor.

## Example

If `h : P ∨ Q` is a hypothesis, then `cases h with hp hq` will turn one goal
into two goals, one with a hypothesis `hp : P` and the other with a
hypothesis `hq : Q`.
"
NewTactic tauto cases

LemmaDoc MyNat.eq_zero_of_add_right_eq_zero as "eq_zero_of_add_right_eq_zero" in "Add" "
  A proof that $a+b=0 \\implies a=0$.
"

-- **TODO** why `add_eq_zero_right` and not `add_right_eq_zero`?
-- https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/eq_zero_of_add_eq_zero_right/near/395716874

/-- If $a+b=0$ then $a=0$. -/
Statement eq_zero_of_add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  Hint "We want to deal with the cases `b = 0` and `b ≠ 0` separately,
  so start with `cases b with d`."
  cases b with d
  intro h
  rw [add_zero] at h
  exact h
  intro h
  rw [add_succ] at h
  symm at h
  apply zero_ne_succ at h
  tauto

Conclusion "Well done!"
