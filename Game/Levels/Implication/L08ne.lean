import Game.Levels.Implication.L07intro2

World "Implication"
Level 8
Title "≠"

TheoremTab "Peano"

namespace MyNat

Introduction
"We still can't prove `2 + 2 ≠ 5` because we have not talked about the
definition of `≠`. In Lean, `a ≠ b` is *notation* for `a = b → False`.
Here `False` is a generic false proposition, and `→` is Lean's notation
for \"implies\". In logic we learn
that `True → False` is false, but `False → False` is true. Hence
`X → false` is the logical opposite of `X`.

Even though `a ≠ b` does not look like an implication,
you should treat it as an implication. The next two levels will show you how.

`False` is a goal which you cannot deduce from a consistent set of assumptions!
So if your goal is `False` then you had better hope that your hypotheses
are contradictory, which they are in this level.
"

/-- If $x=y$ and $x \neq y$ then we can deduce a contradiction. -/
Statement (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  Hint "Remember that `h2` is a proof of `x = y → False`. Try
  `apply`ing `h2` either `at h1` or directly to the goal."
  apply h2 at h1
  exact h1

DefinitionDoc Ne as "≠" "
  `a ≠ b` is *notation* for `(a = b) → False`.

  The reason this is mathematically
  valid is that if `P` is a true-false statement then `P → False`
  is the logical opposite of `P`. Indeed `True → False` is false,
  and `False → False` is true!

  The upshot of this is that use can treat `a ≠ b` in exactly
  the same way as you treat any implication `P → Q`. For example,
  if your *goal* is of the form `a ≠ b` then you can make progress
  with `intro h`, and if you have a hypothesis `h` of the
  form `a ≠ b` then you can `apply h at h1` if `h1` is a proof
  of `a = b`.

"

NewDefinition Ne

Conclusion "Remember, `x ≠ y` is *notation* for `x = y → False`."
