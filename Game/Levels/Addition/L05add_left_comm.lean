import Game.Levels.Addition.L04add_assoc

World "Addition"
Level 5
Title "add_left_comm"

namespace MyNat

Introduction
"
`add_comm a b` is a proof that `a + b = b + a`. But if your goal
is `a + (b + c) = b + (a + c)` then `rw [add_comm a b]` will not
work, There is no `a + b` in this goal, because of the brackets.

`add_assoc` moves brackets around, and `add_comm` moves variables around.
Use these theorems to solve this level.

Remember that in Lean, `a + b + c` *means* `(a + b) + c`.
"

LemmaDoc MyNat.add_left_comm as "add_left_comm" in "Add"
"`add_left_comm a b c` is a proof that `a + (b + c) = b + (a + c)`."

/-- If $a, b$ and $c$ are arbitrary natural numbers, we have
$a + (b + c) = b + (a + c)$. -/
Statement add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  Hint "To rewrite `h : X = Y` backwards (i.e. to change `Y`s to `X`s
    rather than `X`s to `Y`s) use `rw [← h]`"
  rw [← add_assoc]
  Hint (hidden := true) "Remember that you can do more targetted rewrites by
  adding explicit variables to theorems. For example `rw [add_comm b]` will only
  do rewrites of the form `b + ? = ? + b`."
  rw [add_comm a, add_assoc]
  rfl
LemmaTab "Add"

Conclusion "
You've now seen all the tactics you need to beat the final boss of the game.
You can begin the journey towards this boss by entering Multiplication
World. Or you can go off the beaten track and learn some new tactics in Advanced
Addition World. These tactics let you prove more facts about addition, such as
how to deduce `a = b` from `x + a = x + b`.
"

-- **TODO** choose a better example from advanced addition world once it's written
