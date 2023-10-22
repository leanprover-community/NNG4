import Game.Metadata
import Game.MyNat.TutorialLemmas

World "Tutorial"
Level 4
Title "rewriting backwards"

LemmaTab "numerals"

namespace MyNat

Introduction
"
If `h` is a proof of `X = Y` then `rw [h]` will
turn `X`s into `Y`s. But what if we want to
turn `Y`s into `X`s? To tell the `rw` tactic
we want this, we use a left arrow `←`. Type
`\\l` and then hit the space bar to get this arrow.

Let's prove that $2$ is the number after the number
after $0$ again, this time by changing `succ (succ 0)`
into `2`.
"

/-- $2$ is the number after the number after $0$. -/
Statement : 2 = succ (succ 0) := by
  Hint "Try `rw [← one_eq_succ_zero]` to change `succ 0` into `1`."
  rw [← one_eq_succ_zero]
  Hint "What next?"
  Hint (hidden := true) "Now `rw [← two_eq_succ_one]` will change `succ 1` into `2`."
  rw [← two_eq_succ_one]
  rfl

Conclusion "
Why did we not just define `succ n` to be `n + 1`? Because we have not
even *defined* addition yet! We'll do that in the next level.
"
