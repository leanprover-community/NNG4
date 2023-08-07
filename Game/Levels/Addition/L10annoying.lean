import Game.Levels.Addition.L09add_left_comm

World "Addition"
Level 10
Title "harder goals"

namespace MyNat

Introduction
"
Sometimes Lean wants us to solve much messier addition goals,
where the order of the variables needs to be changed
and the brackets need to be moved around. In this level we learn
an algorithm which will work for an arbitrary such problem. Let's
prove `a + b + (c + d) = a + c + d + b`.

"
Statement
"If $a, b$, $c$ and $d$ are arbitrary natural numbers, we have
$(a + b) + (c + d) = ((a + c) + d) + b."
    (a b c d : ℕ) : a + d + (b + c) = a + b + c + d := by
  Hint "We no longer have to use inducion; `add_assoc` and `add_comm` are
    all the tools we need.
    Start with `repeat rw [add_assoc]` to push all the brackets to the right."
  repeat rw [add_assoc]
  Hint "Now use targetted `rw [add_comm x y]` and `rw [add_left_comm x y]` to
  switch consecutive variables `x` and `y` on the left hand side until everything
  is in the right order. The point is that `add_comm` switches the last two,
  and `add_left-comm` can be used to switch any oher pair of consecutive
  variables."
  Hint (hidden := true) "Start with `add_left_comm d b`, which will switch
  `d` and `b` on the left hand side."
  rw [add_left_comm d b, add_comm d c]
  rfl
LemmaTab "Add"

Conclusion
"
  In the last level we use automation to perform this algorithm
  automatically.
"
