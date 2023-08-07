import Game.Metadata
import Game.MyNat.Definition
import Game.MyNat.DecidableEq

World "Tutorial"
Level 4
Title "Peano axioms"

namespace MyNat

LemmaDoc MyNat.one_eq_succ_zero as "foobar" in "bazqux" "`one_eq_succ_zero is a proof of `1 = succ 0`."
NewLemma MyNat.one_eq_succ_zero

Introduction
"
The goals of the previous levels in the tutorial mentioned things like addition and
multiplication of numbers. But now we start the game itself: building the natural
numbers from scratch. Giuseppe Peano defined these numbers via three axioms:

* `0` is a number.
* If `n` is a number, then the *successor* `succ n` of `n` (that is, the number after `n`) is a number.
* That's it.

\"That's it\" means \"there is no other way to make numbers\". More on this later: we need to
 make sure we've cracked the basics before we start talking about infinity. First let's see if we
 can count to five.

# Does this make a section?

What kind of numbers can we make from Peano's axioms? Well, Peano gives us the number `0` and the
function `succ` taking numbers to numbers. We could apply the function to the number and then get a
 new number `succ 0`, and we could name this number `1`. The theorem `one_eq_succ_zero` says that
 `1 = succ 0`.

We could define `2` to either be `succ 1` or `succ (succ 0)`. Are these two choices definitely
equal? Let's see if we can prove it.
"
/-- $\\operatorname{succ}(1)=\\operatorname{succ}(\\operatorname{succ}(0))$. -/
Statement
    : succ 1 = succ (succ 0) := by
  Hint "You can use `rw` and `one_eq_succ_zero` your assumption `h` to substitute `succ a` with `b`.

  Notes:

  1) We do not need brackets for function application the way we would write
  them in mathematics: `succ b` means $\\operatorname\{succ}(b)$.
  2) If you would want to substitute instead `b` with `succ a`, you can do that
  writing a small `←` (`\\l`, i.e. backslash + small letter L + space)
  before `h` like this: `rw [← h]`."
  Branch
    rw [← one_eq_succ_zero]
    Hint (hidden := true) "Now both sides are identical."
    rfl
  rw [one_eq_succ_zero]
  Hint (hidden := true) "Now both sides are identical…"
  rfl

Conclusion
"
We can now go on to define `2`, `3`, `4` and `5` and create associated
proofs called `two_eq_succ_one`, `three_eq_succ_two` and so on.

Why did we call the lemma `one_eq_succ_zero : 1 = succ 0` and not
`succ_zero_eq_one : succ 0 = 1`? There is a reason. At this point
in our development of numbers it's very helpful to have a \"normal form\"
for each number. The normal form we are using for a number `n` is
`succ (succ (succ (... (succ 0)))...)` with `n` `succ`s. The number
`1` is not in this form. The lemma changes `1` into its normal form.
Similarly `three_eq_succ_two` directs `3` towards its normal form.
"
