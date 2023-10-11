import Game.Levels.Implication.L07intro2

World "Implication"
Level 8
Title "≠"

LemmaTab "Peano"

namespace MyNat

Introduction
"We still can't prove `2 + 2 ≠ 5` because we have not talked about the
definition of `≠`. In Lean, `a ≠ b` is *defined* to mean `a = b → False`.
Here `False` is a generic false proposition, and this definition works
because `True → False` is false, but `False → False` is true.

Even though `a ≠ b` does not look like an implication,
you should treat it as an implication. The next two levels will show you how.

`False` is a goal which you cannot deduce from a consistent set of assumptions!
So if your goal is `False` then you had better hope that your hypotheses
are contradictory, which they are in this level.
"

/-- If $x=y$ and $x \neq y$ then we can deduce a contradiction. -/
Statement (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  Hint "Try `apply`ing `h2` either `at h1` or directly to the goal."
  apply h2 at h1
  exact h1

Conclusion "Remember, `x ≠ y` is *notation* for `x = y → False`"
