import Game.Metadata
import Game.MyNat.Addition
import Game.MyNat.DecidableEq
World "Addition"
Level 2
Title "One add one is two."

--namespace MyNat
namespace MyNat

Introduction
"
Before we embark on $2+2=4$ let's go through `1 + 1 = 2` because there's a catch:
"

Statement MyNat.one_add_one
"$2+1=3$."
    : (1 : ℕ) + 1 = 2 := by
  Hint "Go ahead and start with `rw [one_eq_succ_zero]`. Do you see what it does?"
  Branch
    rw [one_eq_succ_zero]
    Hint "It has rewritten both of the `1`s. Finish the goal from here
    and you'll notice that you have to rewrite another one later: rewriting that first `1`
    is a step in the wrong direction. Count the number of rewrites. Now go into editor
    mode and change `rw [one_eq_succ_zero]` to cel your `succ 0`. You can avoid this with `nth_rewrite`. "
  nth_rewrite 2 [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]
  rw [two_eq_succ_one]
  rfl

LemmaTab "Add"

Conclusion
"
  Are you up for the first sub-boss `2 + 2 = 4`?
"
