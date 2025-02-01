import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual

World "LessThan"
Level 1
Title ""

namespace MyNat

Introduction
"
`a < b` is a stronger statment that `a ≤ b`, meaning that `a ≤ b` is *at least as true* as
`a < b`.  We write this as `(a < b) → (a ≤ b)`.  We prove this here.
"



/--
If `a < b`, then `a ≤ b`.  We state and prove this here.
-/
TheoremDoc MyNat.le_of_lt as "le_of_lt" in "<"

/-- If a b are natural numbers, then $a \le b \Rightarrow a \ne b$. -/
Statement le_of_lt (a b: ℕ) : a < b →  a ≤ b := by
  intro ⟨h0,_h1⟩
  exact h0

TheoremTab "<"


