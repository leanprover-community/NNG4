import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual
import Game.Levels.LessThan.A_L01_lt_irrefl


World "LessThan"
Level 2
Title "ne_of_lt"

namespace MyNat

Introduction
"
`a < b` is a stronger statment that `a ≠ b`, meaning that `a ≠  b` is *at least as true* as
`a < b`.  We write this as `(a < b) → (a ≠ b)`.  We prove this here.

"


/--  ne_of_lt a b is proof that if a < b then a ≠ b -/
TheoremDoc MyNat.ne_of_lt as "ne_of_lt" in "<"

/-- If a b are natural numbers, then `a < b → a ≠ b`. -/
Statement ne_of_lt (a b: ℕ) : a < b →  a ≠ b := by
    intro h hab
    Branch
      cases h with n hn
      Hint "You can make this work but it is more work.  You might have
      to use `add_right_eq_self` again"
      rw [hab,succ_add,←add_succ] at hn
      have h1 : succ n = 0 := add_right_eq_self b (succ n) hn.symm
      have h2 := succ_ne_zero n
      exact h2 h1
    rw [hab] at h
    Hint "Now use `have h2 := lt_irrefl {b}."
    have h2 := lt_irrefl b
    Hint "You can take it from here"
    exact h2 h


TheoremTab "<"

Conclusion"For an added challenge, do this proof by immediately
invoking the `contrapose!` tactic."

