import Game.Levels.Addition
import Game.MyNat.AdvAddition

World "AdvAddition"
Level 2
Title "`assumption` practice."

namespace MyNat

Introduction "Sometimes the goal is not *exactly* a hypothesis.
We can then use rewrites to fix things up."

/-- Assuming $\operatorname{succ}(x)=\operatorname{succ}(3)$, we have $x+1=4$. -/
Statement (x : ℕ) (h : x + 1 = y + 1) : succ x = succ y := by
  Hint "Rewrite `succ_eq_add_one` twice, to change the goal
  into the assumption."
  repeat rw [succ_eq_add_one]
  Hint "Now you could finish with `rw [h]` then `rfl`, but `assumption`
  does it in one line."
  assumption

Conclusion "You could instead do `repeat rw [← succ_eq_add_one] at h` to change
the hypothesis into the goal."
