import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial.L05add_succ

World "Tutorial"
Level 6
Title "2+2=4"

open MyNat

Introduction
" Good luck!

  One last hint. If `h : X = Y` then `rw [h]` will change *all* `X`s into `Y`s.
  If you only want to one of them, say the 3rd one, then use
  `nth_rewrite 3 [h]`.
"
namespace MyNat

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

TacticDoc nth_rewrite "
## Summary

If `h : X = Y` and there are several `X`s in the goal, then
`nth_rewrite 3 [h]` will just change the third `X` to a `Y`.

## Example

If the goal is `2 + 2 = 4` then `nth_rewrite 2 [two_eq_succ_one]`
will change the goal to `2 + succ 1 = 4`. In contrast, `rw [two_eq_succ_one]`
will change the goal to `succ 1 + succ 1 = 4`.
"

NewTactic nth_rewrite

Conclusion
"

  Here is an example proof showing off various techniques. You can copy
  and paste it directly into Lean if you switch into editor mode, and then
  you can inspect it by clicking around within the proof.
  Click on `</>` and `>_` in the top right to switch between editor mode
  and command line mode.

```lean
nth_rewrite 2 [two_eq_succ_one]
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
