import Game.Levels.Addition.L01zero_add


World "Addition"
Level 2
Title "succ_add"

namespace MyNat

Introduction
"
Oh no! On the way to `add_comm`, a wild `succ_add` appears. `succ_add a b`
is the proof that `succ(a) + b = succ(a + b)` for `a` and `b` numbers.
This result is what's standing in the way of `x + y = y + x`. Again
we have the problem that we are adding `b` to things, so we need
to split into the cases where `b = 0` and `b` is a successor.
"

LemmaDoc MyNat.succ_add as "succ_add" in "Add"
"`succ_add a b` is a proof that `succ a + b = succ (a + b)`."

/--
For all natural numbers $a, b$, we have
$ \operatorname{succ}(a) + b = \operatorname{succ}(a + b)$.
-/
Statement succ_add (a b : ℕ) : succ a + b = succ (a + b)  := by
  Hint (hidden := true) "You might want to think about whether induction
  on `a` or `b` is the best idea."
  Branch
    induction a with d hd
    Hint "Induction on `a` will not work here. You are still stuck with an `+ b`.
    I suggest you delete this line and try a different approach."
  induction b with d hd
  · rw [add_zero]
    rw [add_zero]
    rfl
  · rw [add_succ, add_succ, hd]
    rfl

LemmaTab "Add"

Conclusion "
Well done! You now have enough tools to tackle the main boss of this level.
"
