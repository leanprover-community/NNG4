import Game.Metadata
import Game.MyNat.Definition
import Game.MyNat.TutorialLemmas

World "Tutorial"
Level 3
Title "Numbers"

namespace MyNat

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


LemmaDoc MyNat.one_eq_succ_zero as "one_eq_succ_zero" in "012"
"`one_eq_succ_zero` is a proof of `1 = succ 0`."

LemmaDoc MyNat.two_eq_succ_one as "two_eq_succ_one" in "012"
"`two_eq_succ_one` is a proof of `2 = succ 1`."

LemmaDoc MyNat.three_eq_succ_two as "three_eq_succ_two" in "012"
"`three_eq_succ_two` is a proof of `3 = succ 2`."

LemmaDoc MyNat.four_eq_succ_three as "four_eq_succ_three" in "012"
"`four_eq_succ_three` is a proof of `4 = succ 3`."

NewDefinition MyNat
NewLemma MyNat.one_eq_succ_zero MyNat.two_eq_succ_one MyNat.three_eq_succ_two
  MyNat.four_eq_succ_three

Introduction
"
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

The *proof* that `2 = succ 1` is called `two_eq_succ_one`.
Check out the \"012\" tab in the list of lemmas on the right
for this and other proofs.

Let's prove that $2$ is the number after the number after zero.
"
/-- $2$ is the number after the number after $0$. -/
Statement
    : 2 = succ (succ 0) := by
  Hint "Start with `rw [two_eq_succ_one]` to begin to break `2` down into its definition."
  rw [two_eq_succ_one]
  Hint "Can you take it from here?"
  Hint (hidden := true) "Next turn `1` into `succ 0` with `rw [one_eq_succ_zero]`."
  rw [one_eq_succ_zero]
  Hint (hidden := true) "Now finish the job with `rfl`."
  rfl

LemmaTab "012"

Conclusion
"
Note that you can do `rw [two_eq_succ_one, one_eq_succ_zero]`
and then `rfl` to solve this level in two lines.
"
