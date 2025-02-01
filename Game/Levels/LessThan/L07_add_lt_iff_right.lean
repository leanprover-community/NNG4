import Game.Levels.LessThan.L06_add_lt_iff_left

World "LessThan"
Level 7
Title "x + a  < x + b ↔ a < b"

namespace MyNat

/-- `le_succ_self x` is a proof that `x ≤ succ x`. -/
TheoremDoc MyNat.add_lt_iff_right as "add_lt_iff_right" in "<"

--Introduction "If you `use` the wrong number, you get stuck with a goal you can't prove.
--What number will you `use` here?"

/-- If $x$ is a number, then $x \le \operatorname{succ}(x)$. -/
Statement add_lt_iff_right {a b c : MyNat} :
    a + b < c + b ↔ a < c := by
 rw [add_comm]
 rw [add_comm c b]
 exact @MyNat.add_lt_iff_left b a c


TheoremTab "<"

Conclusion ""

