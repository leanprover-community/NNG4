import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessThan.L01_lt_iff_not_le

World "LessThan"
Level 2
Title ""

namespace MyNat


Introduction
""

/--

-/
TheoremDoc MyNat.lt_irrefl as "lt_irrefl" in "<"

/-- If $x$ is a number, then $x \le x$. -/
Statement lt_irrefl (x : ℕ) : ¬(x < x) := by
  intro h0
  rw [MyNat.lt_iff_not_le x] at h0
  apply h0
  exact MyNat.le_refl x

TheoremTab "<"
