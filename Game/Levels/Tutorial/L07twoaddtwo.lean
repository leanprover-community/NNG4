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

/-- $2+2=4$. -/
Statement foo : (2 : ℕ) + 2 = 4 := by
  rw [two_eq_succ_one, add_succ, one_eq_succ_zero, add_succ, add_zero, four_eq_succ_three,
    three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  rfl

Conclusion
"

  Here are some example proofs. Copy and paste them into editor mode if you want
  to inspect how they work.

```
  nth_rewrite 2 [two_eq_succ_one]
  rw [add_succ]
  rw [two_add_one_eq_three]
  rw [four_eq_succ_three]
  rfl
```

```
  rw [four_eq_succ_three]
  rw [← two_add_one_eq_three]
  rw [← add_succ]
  rw [← two_eq_succ_one]
  rfl
```

```
  rw [two_eq_succ_one, add_succ, one_eq_succ_zero, add_succ, add_zero, four_eq_succ_three,
    three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  rfl
```


You have finished tutorial world! If you're happy, let's move onto Addition World,
and learn about proof by induction.
"
