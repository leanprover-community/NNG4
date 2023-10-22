import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial.L07add_succ

World "Tutorial"
Level 8
Title "2+2=4"

LemmaTab "numerals"

namespace MyNat

TacticDoc nth_rewrite "
## Summary

If `h : X = Y` and there are several `X`s in the goal, then
`nth_rewrite 3 [h]` will just change the third `X` to a `Y`.

## Example

If the goal is `2 + 2 = 4` then `nth_rewrite 2 [two_eq_succ_one]`
will change the goal to `2 + succ 1 = 4`. In contrast, `rw [two_eq_succ_one]`
will change the goal to `succ 1 + succ 1 = 4`.
"

NewHiddenTactic nth_rewrite

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
Below is an example proof showing off various techniques. You can copy
and paste it directly into Lean if you switch into editor mode, and then
you can inspect it by clicking around within the proof or moving your cursor
down the lines.
Click on `</>` and `>_` in the top right to switch between editor mode
and command line mode. Switch back to command line mode
when you've finished, if you prefer to see hints.

```lean
nth_rewrite 2 [two_eq_succ_one] -- only change the second `2` to `succ 1`.
rw [add_succ]
rw [one_eq_succ_zero]
rw [add_succ, add_zero] -- two rewrites at once
rw [← three_eq_succ_two] -- change `succ 2` to `3`
rw [← four_eq_succ_three]
rfl
```

You have finished tutorial world! Now let's move onto Addition World,
and learn the `induction` tactic.
"
