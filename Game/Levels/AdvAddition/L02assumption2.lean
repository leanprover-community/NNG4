import Game.Levels.Addition
import Game.MyNat.AdvAddition

World "AdvAddition"
Level 2
Title "`assumption` practice."

namespace MyNat

Introduction "If the goal is not *exactly* a hypothesis, we can sometimes
use rewrites to fix things up."

/-- Assuming $0+x=(0+y)+2$, we have $x=y+2$. -/
Statement (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  Hint "Rewrite `zero_add` at `h` twice, to change `h` into the goal."
  repeat rw [zero_add] at h
  Hint "Now you could finish with `rw [h]` then `rfl`, but `assumption`
  does it in one line."
  assumption
