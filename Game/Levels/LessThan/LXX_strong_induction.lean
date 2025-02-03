import Game.Levels.LessThan.L08_lt_trans

World "LessThan"
Level 9
Title "strong induction"

TheoremTab "<"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.strong_induction as "strong_induction" in "<"

Introduction ""

/-- If $\operatorname{succ}(x) \lt \operatorname{succ}(y)$ then $x \lt y$. -/
-- Statement weak_induction {P : ℕ → Prop} (h0 : P MyNat.zero) (hk : ∀ n : ℕ, P n → P (n.succ)) : ∀ n : ℕ, P n := by
--   intro n
--   induction n with k hl
--   exact h0
--   exact hk k hl

Statement strong_induction {P : ℕ → Prop} (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P (n)) : ∀ z : ℕ, P n := by
  intro h1
  induction n with k hk
  specialize h0 0
  apply h0
  intro m hm
  have h1 := lt_iff_not_le
  rw [lt_iff_not_le] at hm
  sorry
  



Conclusion "
Here's my proof:
```
something
```
"
