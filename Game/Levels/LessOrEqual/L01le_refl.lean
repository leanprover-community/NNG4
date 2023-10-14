import Game.Metadata
import Game.MyNat.LE
import Game.Tactic.Use
import Game.Levels.AdvAddition

World "LessOrEqual"
Level 1
Title "The `use` tactic"

namespace MyNat

TacticDoc use "
## Summary

The `use` tactic makes progress with goals which claim something *exists*.
If the goal claims that some `x` exists with some property, and you know
that `x = 37` will work, then `use 37` will make progress.

Because `a ≤ b` is notation for \"there exists `c` such that `b = a + c`\",
you can make progress on goals of the form `a ≤ b` by `use`ing the
number which is morally `b - a`.
"

NewTactic use

Introduction
"
`a ≤ b` is *notation* for `∃ c, b = a + c`. This \"backwards E\"
means \"there exists\". So `a ≤ b` means that there exists
a number `c` such that `b = a + c`. This definition works
because there are no negative numbers in this game.

To *prove* an \"exists\" statement, use the `use` tactic.
Let's see an example.
"

LemmaDoc MyNat.le_refl as "le_refl" in "≤" "
`le_refl x` is a proof of `x ≤ x`.

The reason for the name is that this lemma is \"reflexivity of $\\le$\"
"

NewLemma MyNat.le_refl

/-- If $x$ is a number, then $x \\le x$. -/
Statement le_refl (x : ℕ) : x ≤ x := by
  Hint "The reason `x ≤ x` is because `x = x + 0`.
  So you should start this proof with `use 0`."
  use 0
  Hint "You can probably take it from here."
  rw [add_zero]
  rfl


LemmaTab "≤"
