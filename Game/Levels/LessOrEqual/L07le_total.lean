import Game.Levels.LessOrEqual.L06le_antisymm

World "LessOrEqual"
Level 7
Title "x ≤ y or y ≤ x"

namespace MyNat

LemmaDoc MyNat.le_total as "le_total" in "≤" "
`le_total x y` is a proof that `x ≤ y` or `y ≤ x`.
"

NewLemma MyNat.le_total

Introduction "
This is I think the toughest level yet. We haven't talked about \"or\" at all,
but here's everything you need to know.

1) The notation for \"or\" is `∨`. You won't need to type it, but you can
type it with `\\or`.

2) If you have an \"or\" statement in the *goal*, then two tactics made
progress: `left` and `right`. But don't choose a direction unless your
hypotheses guarantee that it's the right one.

3) If you have an \"or\" statement as a *hypothesis* `h`, then
`cases h with h1 h2` will create two goals, one where you went left,
and the other where you went right.
"

/-- If $x \leq y$ and $y \leq z$, then $x \leq z$. -/
Statement le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction y with d hd
  right
  exact zero_le x
  cases hd with h1 h2
  left
  cases h1 with e h1
  rw [h1]
  use e + 1
  rw [succ_eq_add_one, add_assoc]
  rfl
  cases h2 with e h2
  rw [h2]
  cases e with a
  left
  rw [add_zero]
  use 1
  exact succ_eq_add_one d
  right
  use a
  rw [add_succ, succ_add, add_comm]
  rfl




LemmaTab "≤"

Conclusion "
Here's a four line proof:
```
rcases hxy with ⟨a, rfl⟩
rcases hyz with ⟨b, rfl⟩
use a + b
exact add_assoc x a b
```

A passing mathematician remarks that with reflexivity and transitivity out of the way,
you have proved that `≤` is a *preorder* on `ℕ`.
"
