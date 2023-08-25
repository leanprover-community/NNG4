import Game.Metadata
import Game.MyNat.Definition
import Game.MyNat.DecidableEq

World "Tutorial"
Level 3
Title "Numbers"

namespace MyNat

Introduction
"
The goals of the previous levels in the tutorial mentioned things like addition and
multiplication of numbers. But now we start the game itself: building
numbers from scratch. Our definition of (natural) numbers is based on
Giuseppe Peano's, and consists of three axioms:

* `0` is a number.
* If `n` is a number, then the *successor* `succ n` of `n` (that is, the number after `n`) is a number.
* That's it.

The final boss of this world is `2 + 2 = 4`. If you can prove this theorem,
you've mastered the basics. Our problem right now is that we cannot even *state*
the theorem because we haven't yet defined `2` or `+` or `4`. Let's worry about `+`
later; before we learn to add we learn to count, so let's count to four.

# Counting to four.

What kind of numbers can we make from Peano's axioms? Well, Peano gives us the number `0` for free,
but the only other thing we have is this successor function, which eats a number and
spits out the number after it. So we could *define* `1` to be `succ 0` (Note that Lean
does not *need* brackets for function inputs, although you can use them if you want after the space).

Let's define `2` to be `succ 1`, `3` to be `succ 2` and `4` to be `succ 3`.
You can think of a statement like `3 = succ 2` as an axiom or hypothesis, and
this game has a special name for this hypothesis, which is `three_eq_succ_two`. This should
be the first theorem you rewrite with in the proof of the theorem below;
the natural flow of the proof is to break down the larger more complex numbers
into simpler ones, and ultimately down to a hugely inefficient \"normal form\"
`succ (succ (succ (succ ... 0))..)

Use the `rw` tactic to prove that 3 is the number after the number after the number after 0.

"
/-- $3=\operatorname{succ}\operatorname{succ}(\operatorname{succ}(0))$. -/
Statement
    : 3 = succ (succ (succ 0)) := by
  Hint "Take a look at the names of the proofs in the `numerals` tab on the right.
  Start to think about how to guess the names of proofs automatically."
  rw [three_eq_succ_two]
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  rfl

LemmaDoc MyNat.one_eq_succ_zero as "one_eq_succ_zero" in "numerals"
"`one_eq_succ_zero` is a proof of `1 = succ 0`."

LemmaDoc MyNat.two_eq_succ_one as "two_eq_succ_one" in "numerals"
"`two_eq_succ_one is a proof of `2 = succ 1`."

LemmaDoc MyNat.three_eq_succ_two as "three_eq_succ_two" in "numerals"
"`three_eq_succ_two is a proof of `3 = succ 2`."

LemmaDoc MyNat.four_eq_succ_three as "four_eq_succ_three" in "numerals"
"`four_eq_succ_three is a proof of `4 = succ 3`."

LemmaDoc MyNat.five_eq_succ_four as "five_eq_succ_four" in "numerals"
"`five_eq_succ_four is a proof of `5 = succ 4`."

NewLemma MyNat.one_eq_succ_zero MyNat.two_eq_succ_one MyNat.three_eq_succ_two
  MyNat.four_eq_succ_three MyNat.five_eq_succ_four
LemmaTab "numerals"
