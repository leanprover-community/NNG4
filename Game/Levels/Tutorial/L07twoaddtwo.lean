import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial.L06twoaddone
World "Tutorial"
Level 7
Title "2+2=4"

open MyNat

Introduction
"
  Use your tools. You only have two tactics, `rw` and `rfl`, but you have
  a lot of proofs which you can rewrite. Look at your collection of proofs
  on the right hand side. As you progress through the game, you will get
  many more.

  One last hint. If `h : X = Y` then `rw [h]` will change *all* `X`s into `Y`s.
  If you only want to change one of them, say the 37th one, then use
  `nth_rewrite 37 [h]`
"
namespace MyNat

/-- $2+2=4$. -/
Statement : (2 : ℕ) + 2 = 4 := by
  Hint (hidden := true) "`nth_rewrite 2 [two_eq_succ_one]` is I think quicker than `rw [two_eq_succ_one]`."
  nth_rewrite 2 [two_eq_succ_one]
  Hint (hidden := true) "Now you can `rw [add_succ]`"
  rw [add_succ]
  Hint (hidden := true) "There is now a short way and a long way..."
  rw [two_add_one_eq_three]
  rw [four_eq_succ_three]
  rfl

Conclusion
"
You have finished tutorial world! If you're happy, let's move onto Addition World,
and learn about proof by induction.

## Inspection time

If you want to examine your proofs, toggle \"Editor mode\" and click somewhere
inside the proof to see the state of Lean's brain at that point.
"
