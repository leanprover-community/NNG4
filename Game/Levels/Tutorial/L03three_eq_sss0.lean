import Game.Metadata
import Game.MyNat.Definition
import Game.MyNat.DecidableEq

World "Tutorial"
Level 3
Title "Numbers"

namespace MyNat

Introduction
"

# The birth of number.

Now you know some tactics, let's begin the game. We were talking
about numbers in the previous levels, but now let's go back to basics.
What are numbers? Numbers in Lean can be defined by three axioms, an
idea going back to Giuseppe Peano. Here are the first two of them.

* `0` is a number.
* If `n` is a number, then the *successor* `succ n` of `n` (that is, the number after `n`)
is a number.

What numbers can we make in this system? Let's figure out how to count,
and name a few small numbers.

# Counting to four.

The first axiom gives us the number `0` for free. The other gives us
the successor function `succ`. If we apply this function to `0`
then we get a new number `succ 0`, the number after `0`. Let's
call this new number `1`.

We can define `2` to be `succ 1`, then set `3 = succ 2` and `4 = succ 3`.
This gives us plenty of numbers to be getting along with.

You can think of a statement like `3 = succ 2` as an axiom or hypothesis or
theorem, and this game has a special name for the proof of this theorem:
it's called `three_eq_succ_two`.

Use the `rw` tactic to prove that 3 is the number after the number after the number after 0.

"
/-- $3=\operatorname{succ}\operatorname{succ}(\operatorname{succ}(0))$. -/
Statement
    : 3 = succ (succ (succ 0)) := by
  Hint "Use the lemmas in the *numerals* section to break `3` down into
  basic pieces."
  rw [three_eq_succ_two]
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  rfl

LemmaDoc MyNat.one_eq_succ_zero as "one_eq_succ_zero" in "numerals"
"`one_eq_succ_zero` is a proof of `1 = succ 0`."

LemmaDoc MyNat.two_eq_succ_one as "two_eq_succ_one" in "numerals"
"`two_eq_succ_one` is a proof of `2 = succ 1`."

LemmaDoc MyNat.three_eq_succ_two as "three_eq_succ_two" in "numerals"
"`three_eq_succ_two` is a proof of `3 = succ 2`."

LemmaDoc MyNat.four_eq_succ_three as "four_eq_succ_three" in "numerals"
"`four_eq_succ_three` is a proof of `4 = succ 3`."

LemmaDoc MyNat.five_eq_succ_four as "five_eq_succ_four" in "numerals"
"`five_eq_succ_four` is a proof of `5 = succ 4`."

-- **todo** do we need 5?

NewLemma MyNat.one_eq_succ_zero MyNat.two_eq_succ_one MyNat.three_eq_succ_two
  MyNat.four_eq_succ_three MyNat.five_eq_succ_four
LemmaTab "numerals"

Conclusion
"
Why did we not just define `succ n` to be `n + 1`? Because we have not
even *defined* addition yet! We'll do that in the next level.
"
