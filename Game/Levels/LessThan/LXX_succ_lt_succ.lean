import Game.Levels.LessThan.L04_lt_trans

World "LessThan"
Level 5
Title "succ x < succ y → x < y"

TheoremTab "<"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.succ_lt_succ as "succ_lt_succ" in "<"

Introduction ""

/-- If $\operatorname{succ}(x) \lt \operatorname{succ}(y)$ then $x \lt y$. -/
Statement succ_lt_succ (x y : ℕ) (hx : succ x < succ y) : x < y := by
  rcases hx with ⟨a,ha⟩
  use a
  rw [add_succ,succ_add] at ha
  have h1 := succ_inj y _  ha
  rw [h1]
  rw [add_succ]
  rfl



Conclusion "
Here's my proof:
```
something
```
"
