import Game.Levels.Addition.L08add_assoc

World "Addition"
Level 9
Title "add_left_comm"

namespace MyNat

Introduction
"
`add_comm a b` is a proof that `a + b = b + a`. But if your goal
is `a + (b + c) = b + (a + c)` then `rw [add_comm a b]` will not
work, because nowhere in this goal is there an `a + b`. Although
it's harder to see,`rw [add_comm b c]` will not work on a goal
of the form `a + b + c = a + c + b`, as `a + b + c` actually
means `(a + b) + c`, so again the brackets are in the wrong place.

However, associativity (which moves brackets around) and commutativity
(which swaps variables around) can in theory be used to prove goals
like `(d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h`.
Let's start with a simpler one. Can you do it in three rewrites?
"

LemmaDoc MyNat.add_left_comm as "add_left_comm" in "Add"
"`add_left_comm a b c` is a proof that `a + (b + c) = b + (a + c)`."

/-- If $a, b$ and $c$ are arbitrary natural numbers, we have
$a + (b + c) = b + (a + c)$. -/
Statement add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  Hint "Don't use induction; `add_assoc` and `add_comm` are all the tools you need.
    Remember that to rewrite `h : X = Y` backwards (i.e. to change `Y`s to `X`s
    rather than `X`s to `Y`s) use `rw [←h]`"
  Hint (hidden := true) "Remember that you can do more targetted rewrites by
  adding explicit variables to theorems. For example `rw [add_comm b]` will only
  do rewrites of the form `b + ? = ? + b`."
  rw [←add_assoc, add_comm a, add_assoc]
  rfl
LemmaTab "Add"

Conclusion
"
If you have got this far, then you have become very good at
manipulating equalities in Lean. Now let's think about the
annoying level `a + b + c + d = a + c + d + b` and try and come
up with an *algorithm* which will solve this problem for us,
so we don't have to write `rw [add_assoc]` five times.
"
