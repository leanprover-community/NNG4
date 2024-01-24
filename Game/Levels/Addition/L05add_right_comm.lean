import Game.Levels.Addition.L04add_assoc

World "Addition"
Level 5
Title "add_right_comm"

namespace MyNat

Introduction
"
`add_comm b c` is a proof that `b + c = c + b`. But if your goal
is `a + b + c = a + c + b` then `rw [add_comm b c]` will not
work! Because the goal means `(a + b) + c = (a + c) + b` so there
is no `b + c` term *directly* in the goal.

Use associativity and commutativity to prove `add_right_comm`.
You don't need induction. `add_assoc` moves brackets around,
and `add_comm` moves variables around.

Remember that you can do more targetted rewrites by
adding explicit variables as inputs to theorems. For example `rw [add_comm b]`
will only do rewrites of the form `b + ? = ? + b`, and `rw [add_comm b c]`
will only do rewrites of the form `b + c = c + b`.
"

/-- `add_right_comm a b c` is a proof that `(a + b) + c = (a + c) + b`

In Lean, `a + b + c` means `(a + b) + c`, so this result gets displayed
as `a + b + c = a + c + b`.
-/
TheoremDoc MyNat.add_right_comm as "add_right_comm" in "+"

/-- If $a, b$ and $c$ are arbitrary natural numbers, we have
$(a + b) + c = (a + c) + b$. -/
Statement add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_comm b, add_assoc]
  rfl

TheoremTab "+"

Conclusion "
You've now seen all the tactics you need to beat the final boss of the game.
You can begin the journey towards this boss by entering Multiplication World.

Or you can go off the beaten track and learn some new tactics in Implication
World. These tactics let you prove more facts about addition, such as
how to deduce `a = 0` from `x + a = x`.

Click \"Leave World\" and make your choice.
"
