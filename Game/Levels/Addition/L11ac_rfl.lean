import Game.Levels.Addition.L09add_left_comm

World "Addition"
Level 11
Title "The final boss"

namespace MyNat

Introduction
"
We saw in the last level that by performing an algorithm repeating `add_assoc`
and then applying `add_comm` and `add_left_comm` to sort variables, enables
us to manually prove arbitrary identities involving addition of natural
numbers. Let's now write a tactic which automates this.

**TODO** ac_rfl tactic
"


/-- If $a, b,\\ldots h$ are arbitrary natural numbers, we have
$(d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h$. -/
Statement
    (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_assoc, add_left_comm, add_comm]
LemmaTab "Add"

Conclusion
"
  Congratulations! You finished addition world. Now go back to the overworld by clicking the
  home button in the top left. If you want to press on to the final boss
  of the game then go to Multiplication world next. If you are in no hurry, and would like
  to learn some more tactics, then you can try Advanced Addition World.
"
