import Game.Metadata
import Game.MyNat.Definition


World "Tutorial"
Level 3
Title "Peano axioms"

open MyNat

Introduction
"
The goals of the previous levels in the tutorial mentioned things like addition and multiplication of numbers. But now we start the game itself: building the natural numbers from scratch. Giuseppe Peano defined these numbers via three axioms:

* `0` is a number.
* If `n` is a number, then the *successor* `succ n` of `n` (that is, the number after `n`) is a number.
* That's it.

Informally, "That's it" means "there is no other way to make numbers". We will see a precise statement of "That's it" later on.

# Does this make a section?

What kind of numbers can we make from Peano's axioms? Well, Peano gives us the number `0` and the function `succ` taking numbers to numbers. We could apply the function to the number and then get a new number `succ 0`, and we could name this number `1`. The theorem `one_eq_succ_zero` says that `1 = succ 0`.

We could define `2` to either be `succ 1` or `succ (succ 0)`. Are these two choices definitely equal? Let's see if we can prove it.

Statement
"$\\operatorname{succ}(1)=\\operatorname{succ}(\\operatorname{succ}(0))$."
    succ 1 = succ (succ 0) := by
  Hint "You can use `rw` and your assumption `{h}` to substitute `succ a` with `b`.

  Notes:

  1) We do not need brackets for function application the way we would write
  them in mathematics: `succ b` means $\\operatorname\{succ}(b)$.
  2) If you would want to substitute instead `b` with `succ a`, you can do that
  writing a small `←` (`\\l`, i.e. backslash + small letter L + space)
  before `h` like this: `rw [← h]`."
  Branch
    simp? -- TODO: `simp` should not make progress.
  Branch
    rw [← h]
    Hint (hidden := true) "Now both sides are identical…"
  rw [h]
  Hint (hidden := true) "Now both sides are identical…"
  rfl

Conclusion
"
You may also be wondering why we keep writing `succ b` instead of `b + 1`.
This is because we haven't defined addition yet!
On the next level, the final level of Tutorial World,
we will introduce addition, and then we'll be ready to enter Addition World.
"



