import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial.L07add_succ

World "Tutorial"
Level 8
Title "2+2=4"

TheoremTab "012"

namespace MyNat

Introduction
" Good luck!

  One last hint. If `h : X = Y` then `rw [h]` will change *all* `X`s into `Y`s.
  If you only want to change one of them, say the 3rd one, then use
  `nth_rewrite 3 [h]`.
"

/-- $2+2=4$. -/
Statement : (2 : ℕ) + 2 = 4 := by
  Hint (hidden := true) "`nth_rewrite 2 [two_eq_succ_one]` is I think quicker than `rw [two_eq_succ_one]`."
  nth_rewrite 2 [two_eq_succ_one]
  Hint (hidden := true) "Now you can `rw [add_succ]`"
  rw [add_succ]
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]
  rw [four_eq_succ_three]
  rw [three_eq_succ_two]
  rfl

Conclusion
"
Here is an example proof of 2+2=4 showing off various techniques.

```lean
nth_rewrite 2 [two_eq_succ_one] -- only change the second `2` to `succ 1`.
rw [add_succ]
rw [one_eq_succ_zero]
rw [add_succ, add_zero] -- two rewrites at once
rw [← three_eq_succ_two] -- change `succ 2` to `3`
rw [← four_eq_succ_three]
rfl
```

Optional extra: you can run this proof yourself. Switch the game into \"Editor mode\" by clicking
on the `</>` button in the top right. You can now see your proof
written as several lines of code. Move your cursor between lines to see
the goal state at any point. Now cut and paste your code elsewhere if you
want to save it, and paste the above proof in instead. Move your cursor
around to investigate. When you've finished, click the `>_` button in the top right to
move back into \"Typewriter mode\".

You have finished tutorial world!
Click \"Home\" to go back to the
overworld, and select Addition World, where you will learn
about the `induction` tactic.
"
