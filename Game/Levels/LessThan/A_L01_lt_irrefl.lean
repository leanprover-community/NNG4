import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition

World "LessThan"
Level 1
Title "LessThan is irreflexive"

namespace MyNat


Introduction
"Introduction Needed"

/--`lt_irrefl a` is a proof that `¬(a < a)`.  In words, a natural number `a` is not
less than itself.-/
TheoremDoc MyNat.lt_irrefl as "lt_irrefl" in "<"

/-- If $x$ is a natural number, then $\neg (x \lt x)$. -/
Statement lt_irrefl (x : ℕ) : ¬(x < x) := by
  rintro ⟨n,hn⟩
  rw [succ_add,←add_succ] at hn
  have h1 : succ n = 0 := by
    exact add_right_eq_self x (succ n) hn.symm
  have h2 := succ_ne_zero n
  exact h2 h1

TheoremTab "<"

Conclusion "Conclusion Needed"
