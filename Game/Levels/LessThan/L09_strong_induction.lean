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

-- Statement strong_induction {P : ℕ → Prop} (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P (n)) : ∀ z : ℕ, P z := by
--   intro z
--   revert h0
--   induction z with k hk
--   intro h0
--   specialize h0 0
--   apply h0
--   sorry
--   intro h0
--   have h1 := h0 (succ k)
--   apply h1
--   intro m hm
--   have h2 : m < k ∨ m = k := by sorry
--   rcases h2 with (h2 | h2)
--   specialize h0 m
--   apply h0
--   intro mm hmm



Statement strong_induction_1 {P : ℕ → Prop} (h0 : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P (n)) : ∀ z : ℕ,  P z := by
  have h1 : ∀ z : ℕ, ∀ y : ℕ, y < z → P y := by
    intro z
    induction z with k hk
    intro y hy
    exfalso
    sorry
    intro y hy
    have h1 : y < k ∨ y = k := by sorry
    rcases h1 with (h1 | h1)
    exact hk y h1
    specialize h0 y
    

  intro y
  specialize h1 (succ y) y
  apply h1
  sorry
  
  

Conclusion "
Here's my proof:
```
something
```
"
