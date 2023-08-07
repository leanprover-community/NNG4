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
I'm not sure you're quite ready for `2 + 2 = 4` so let's warm up some
more with `1 + 1 = 2` to see if you can spot a minor problem with our
strategy.
"

Statement
"$1+1=2$."
    : (1 : ℕ) + 1 = 2 := by
  Hint "Go ahead and start with `rw [one_eq_succ_zero]`. Do you see what it does?"
  Branch
    rw [one_eq_succ_zero]
    Hint "It has rewritten both of the `1`s. Finish the goal from here
    and you'll notice that you have to rewrite another one later: rewriting that first `1`
    is a step in the wrong direction. Count the number of rewrites. Now go into editor
    mode and change `rw [one_eq_succ_zero]` to `nth_rewrite 2 [one_eq_succ_zero].
    This tells Lean to only change the second `1` into a `succ 0`."
  nth_rewrite 2 [one_eq_succ_zero]
  Hint "With this revised opening you should be able to solve the level in
    three more rewrites rather than four more."
  rw [add_succ]
  rw [add_zero]
  rw [two_eq_succ_one]
  Hint "Nice! Nearly there."
  rfl

LemmaTab "Add"

Conclusion
"
  Are you now up for the first sub-boss `2 + 2 = 4`?
"
