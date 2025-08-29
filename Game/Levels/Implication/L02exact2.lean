import Game.Levels.Implication.L01exact

World "Implication"
Level 2
Title "`exact` practice."

namespace MyNat

Introduction "If the goal is not *exactly* a hypothesis, we can sometimes
use rewrites to fix things up."

/-- Assuming $0+x=(0+y)+2$, we have $x=y+2$. -/
Statement (x y : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  Hint "You can use `rw [zero_add] at {h}` to rewrite at `{h}` instead
  of at the goal."
  rw [zero_add] at h
  Hint (hidden := true) "Do that again!

  `rw [zero_add] at {h}` tries to fill in
  the arguments to `zero_add` (finding `{x}`) then it replaces all occurences of
  `0 + {x}` it finds. Therefor, it did not rewrite `0 + {y}`, yet."
  rw [zero_add] at h
  Hint "Now you could finish with `rw [{h}]` then `rfl`, but `exact {h}`
  does it in one line."
  exact h

Conclusion "Here's a two-line proof:
```
repeat rw [zero_add] at h
exact h
```
"
