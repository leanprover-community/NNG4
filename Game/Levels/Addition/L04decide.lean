import Game.Metadata
import Game.MyNat.Addition
import Game.MyNat.DecidableEq
World "Addition"
Level 3
Title "Two add two is four."

--namespace MyNat
namespace MyNat

TacticDoc decide "
The `decide` tactic is able to prove goals involving *known numerals*. It is not
good with algebra, so don't give it goals with `x`s in, but it can prove
things like `2 + 2 = 4` and even `20 + 20 = 40` automatically.

When run on `MyNat` goals, the tactic uses the decidable equality instance
on `MyNat` in `Game.MyNat.DecidableEq`. The implementation
is not at all optimised: I just wanted to get something which could beat
humans easily.
"
NewTactic decide

example : (20 : ℕ) + 20 = 40 := by
  decide

Introduction
"
Oh did I mention there was a new tactic? Find it in the blah blah blah.
"
Statement
"$29+35=64."
    : (29 : ℕ) + 35 = 64 := by
  decide

LemmaTab "Add"

Conclusion
"
  The `decide` tactic destroys sub-bosses such as `2 + 2 = 4`.

"
