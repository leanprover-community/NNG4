import Game.Metadata
import Game.MyNat.Addition
import Game.MyNat.DecidableEq
World "Addition"
Level 1
Title "Two add one is three."

namespace MyNat

Introduction
"
Remember Peano's axioms:

* `add_zero x : x + 0 = x`
* `add_succ a b : a + succ b = succ (a + b)

If you don't need precision about exactly what to rewrite, then you can skip the
variables `x` and `a`, `b` when rewriting.

Remember also the definitions of numbers:

* `one_eq_succ_zero : 1 = succ 0`
* `two_eq_succ_one : 2 = succ 1`
etc up to 5.

Can you prove `2 + 1 = 3`?
"

/-- $2+1=3$. -/
Statement : (2 : ℕ) + 1 = 3 := by
  Hint "Which one of Peano's axioms do we ultimately want to use to rewrite that addition?"
  Hint (hidden := true) "change `1` to `succ 0` with a rewrite, and then
  think about Peano's axioms."
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]
  rw [three_eq_succ_two]
  rfl

LemmaDoc MyNat.two_eq_succ_one as "two_eq_succ_one" in "numerals"
"`two_eq_succ_one is a proof of `2 = succ 1`."

LemmaDoc MyNat.three_eq_succ_two as "three_eq_succ_two" in "numerals"
"`three_eq_succ_two is a proof of `3 = succ 2`."

LemmaDoc MyNat.four_eq_succ_three as "four_eq_succ_three" in "numerals"
"`four_eq_succ_three is a proof of `4 = succ 3`."

LemmaDoc MyNat.five_eq_succ_four as "five_eq_succ_four" in "numerals"
"`five_eq_succ_four is a proof of `5 = succ 4`."

NewLemma MyNat.two_eq_succ_one MyNat.three_eq_succ_two
  MyNat.four_eq_succ_three MyNat.five_eq_succ_four
LemmaTab "numerals"

Conclusion
"
Are you up for `2 + 2 = 4`?
"
