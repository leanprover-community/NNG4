import Game.Levels.AdvAddition.Level_4



World "AdvAddition"
Level 5
Title "add_right_cancel"

open MyNat

Introduction
"
The theorem `add_right_cancel` is the theorem that you can cancel on the right
when you're doing addition -- if `a + t = b + t` then `a = b`.
"

Statement MyNat.add_right_cancel
"On the set of natural numbers, addition has the right cancellation property.
In other words, if there are natural numbers $a, b$ and $c$ such that
$$ a + t = b + t, $$
then we have $a = b$."
    (a t b : ℕ) : a + t = b + t → a = b := by
  Hint (hidden := true) "You can either start with `induction t` or with
  `intro` and you will have to do the other one afterwards."
  Branch
    intro h
    Hint "I'd recommend now induction on `t`. Don't forget that `rw [add_zero] at h` can be used
    to do rewriting of hypotheses rather than the goal."
    induction t with d hd
    · Hint "You might have noticed an old `{h}✝` floating
      around in your assumptions. `x✝` marks variables that can't be used
      anymore because a new variable got assigned the name `x`.
      In your case that is because `induction` deleted the old `{h}` when
      it created the `t=0` (or later `succ t`) variants. Just ignore the
      `{h}✝`."
      rw [add_zero] at h
      rw [add_zero] at h
      exact h
    · Hint "You might have noticed an old `{h}✝` floating
      around in your assumptions. `x✝` marks variables that can't be used
      anymore because a new variable got assigned the name `x`.
      In your case that is because `induction` deleted the old `{h}` when
      it created the `succ t` variant. Just ignore the `{h}✝`."
      Branch
        simp at h
        exact hd h
      apply hd
      rw [add_succ] at h
      rw [add_succ] at h
      exact succ_inj h
  induction t with d hd
  · Hint (hidden := true) "You want to look at `intro`."
    Branch
      simp
    intro h
    rw [add_zero] at h
    rw [add_zero] at h
    exact h
  · Hint "Since you called `induction t` first, you now have to call
    `intro` on each of the subgoals."
    Hint (hidden := true) "You want to look at `intro`"
    Branch
      simp
      exact hd
    intro h
    apply hd
    rw [add_succ] at h
    rw [add_succ] at h
    Hint (hidden := true) "At this point `succ_inj` might be useful."
    exact succ_inj h


-- TODO: Display at this level after induction is confusing: old assumption floating in context

LemmaTab "Add"
DisabledTactic simp

Conclusion
"

"
