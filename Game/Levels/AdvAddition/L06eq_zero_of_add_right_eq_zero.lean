import Game.Levels.AdvAddition.L05add_right_eq_self

World "AdvAddition"
Level 6
Title "eq_zero_of_add_right_eq_zero"

LemmaTab "Peano"

namespace MyNat

Introduction
" We have still not proved that if `a + b = 0` then `a = 0` and `b = 0`. Let's finish this
world by proving one of these in this level, and the other in the next.

If you have a hypothesis `h : False` then you are done, because a false statement implies
any statement. You can use the `contradiction` tactic to finish your proof.
"

TacticDoc contradiction "
The `contradiction` tactic will solve any goal, if you have a hypothesis `h : False`.
"
NewTactic contradiction

LemmaDoc MyNat.eq_zero_of_add_right_eq_zero as "eq_zero_of_add_right_eq_zero" in "Add" "
  A proof that $a+b=0 \\implies a=0$.
"

-- **TODO** why `add_eq_zero_right` and not `add_right_eq_zero`?
-- https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/eq_zero_of_add_eq_zero_right/near/395716874

/-- If $a+b=0$ then $a=0$. -/
Statement eq_zero_of_add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  Hint "We want to deal with the cases `b = 0` and `b ≠ 0` separately, so start with `induction b with d hd`
  but just ignore the inductive hypothesis in the `succ d` case :-)"
  induction b with d _ -- don't even both naming inductive hypo
  intro h
  rw [add_zero] at h
  exact h
  intro h
--  clear hd -- **TODO** remove after `cases`
  rw [add_succ] at h
  symm at h
  apply zero_ne_succ at h
  contradiction
