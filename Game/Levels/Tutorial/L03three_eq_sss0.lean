import Game.Metadata
import Game.MyNat.Definition
import Game.MyNat.TutorialLemmas

World "Tutorial"
Level 3
Title "Numbers"

namespace MyNat

Introduction
"

Now you know some tactics, let's begin the game.

## The birth of number.

Numbers in Lean are defined by two rules.

* `0` is a number.
* If `n` is a number, then the *successor* `succ n` of `n` is a number.

The successor of `n` means the number after `n`. Let's learn to
count, and name a few small numbers.

## Counting to four.

`0` is a number, so `succ 0` is a number. Let's call this new number `1`.
Similarly let's define `2 = succ 1`, `3 = succ 2` and `4 = succ 3`.
This gives us plenty of numbers to be getting along with.

The *proof* that `3 = succ 2` is called `three_eq_succ_two`.
Check out the \"numerals\" tab in the list of lemmas on the right,
and rewrite these proofs to deduce that $3$ is the number after the number after
the number after $0$.

"
/-- $3=\operatorname{succ}(\operatorname{succ}(\operatorname{succ}(0)))$. -/
Statement
    : 3 = succ (succ (succ 0)) := by
  Hint "Rewrite the lemmas in the *numerals* section on the right to break `3` down into
  basic pieces."
  Hint (hidden := true) "Start with `rw [three_eq_succ_two]`"
  rw [three_eq_succ_two]
  Hint (hidden := true) "If you're in a hurry, try `rw [two_eq_succ_one, one_eq_succ_zero]`."
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  Hint (hidden := true) "Now finish the job with `rfl`."
  rfl

DefinitionDoc MyNat as "ℕ"
"
`ℕ` is the natural numbers, just called \"numbers\" in this game. It's
defined via two rules:

* `0 : ℕ` (zero is a number)
* `succ (n : ℕ) : ℕ` (the successor of a number is a number)

## Game Implementation

*The game uses its own copy of the natural numbers, called `MyNat` with notation `ℕ`.
It is distinct from the Lean natural numbers `Nat`, which should hopefully
never leak into the natural number game.*"

NewDefinition MyNat

LemmaDoc MyNat.one_eq_succ_zero as "one_eq_succ_zero" in "numerals"
"`one_eq_succ_zero` is a proof of `1 = succ 0`."

LemmaDoc MyNat.two_eq_succ_one as "two_eq_succ_one" in "numerals"
"`two_eq_succ_one` is a proof of `2 = succ 1`."

LemmaDoc MyNat.three_eq_succ_two as "three_eq_succ_two" in "numerals"
"`three_eq_succ_two` is a proof of `3 = succ 2`."

LemmaDoc MyNat.four_eq_succ_three as "four_eq_succ_three" in "numerals"
"`four_eq_succ_three` is a proof of `4 = succ 3`."

NewLemma MyNat.one_eq_succ_zero MyNat.two_eq_succ_one MyNat.three_eq_succ_two
  MyNat.four_eq_succ_three

LemmaTab "numerals"

Conclusion
"
Note that you can do
`rw [three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]`
and then `rfl` to solve this level in two lines.

Why did we not just define `succ n` to be `n + 1`? Because we have not
even *defined* addition yet! We'll do that in the next level.
"
