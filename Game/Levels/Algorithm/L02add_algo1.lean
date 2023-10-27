import Game.Levels.Algorithm.L01add_left_comm

World "Algorithm"
Level 2
Title "making life easier"

LemmaTab "+"

namespace MyNat

Introduction
"
In some later worlds, we're going to see some much nastier levels,
like `(a + a + 1) + (b + b + 1) = (a + b + 1) + (a + b + 1)`.
Brackets need to be moved around, and variables need to be swapped.

In this level, `(a + b) + (c + d) = ((a + c) + b) + d`,
let's forget about the brackets and just think about
the variable order.
To turn `a+b+c+d` into `a+c+d+b` we need to swap `b` and `c`,
and then swap `b` and `d`. But this is easier than you
think with `add_left_comm`.
"

/-- If $a, b$, $c$ and $d$ are numbers, we have
$(a + b) + (c + d) = ((a + c) + d) + b.$ -/
Statement (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  Hint "Start with `repeat rw [add_assoc]` to push all the brackets to the right."
  repeat rw [add_assoc]
  Hint "Now use `rw [add_left_comm b c]` to switch `b` and `c` on the left
  hand side."
  rw [add_left_comm b c]
  Hint "Finally use a targetted `add_comm` to switch `b` and `d`"
  Hint (hidden := true) "`rw [add_comm b d]`."
  rw [add_comm b d]
  rfl

LemmaTab "+"

Conclusion
"
So that's the algorithm: now let's use automation to perform it
automatically.
"
