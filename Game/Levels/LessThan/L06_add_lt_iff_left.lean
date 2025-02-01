import Game.Levels.LessThan.L05_lt_iff_succ_le

World "LessThan"
Level 6
Title "a + x < b + x ↔ a < b"

namespace MyNat

/-- `le_succ_self x` is a proof that `x ≤ succ x`. -/
TheoremDoc MyNat.add_lt_iff_left as "add_lt_iff_left" in "<"

--Introduction "If you `use` the wrong number, you get stuck with a goal you can't prove.
--What number will you `use` here?"

/-- If $x$ is a number, then $x \le \operatorname{succ}(x)$. -/
Statement add_lt_iff_left {a b c : MyNat} :
    a + b < a + c ↔ b < c := by
  have h1 := by calc
    a + b < a + c
      ↔ ¬ ((a + c) ≤ (a + b))  := by sorry
    _ ↔ ¬ (c ≤ b)              := by sorry
    _ ↔ b < c                  := by sorry
  exact h1




TheoremTab "<"

Conclusion ""

