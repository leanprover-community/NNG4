import Game.Levels.LessOrEqual.L04le_zero

World "LessOrEqual"
Level 5
Title "x ≤ y and y ≤ z implies x ≤ z"

namespace MyNat

Introduction "
We have already proved that `x ≤ x`, i.e. that `≤` is *reflexive*. Now let's
prove that it's *transitive*, i.e., that if `x ≤ y` and `y ≤ z` then `x ≤ z`.
"

LemmaDoc MyNat.le_trans as "le_trans" in "≤" "
`le_trans x y z` is a proof that if `x ≤ y` and `y ≤ z` then `x ≤ z`.
More precisely, it is a proof that `x ≤ y → (y ≤ z → x ≤ z)`. In words,
If $x \\le y$ then (pause) if $y \\le z$ then $x \\le z$.

## A note on associativity

In Lean, `a + b + c` means `(a + b) + c`, because `+` is left associative. However
`→` is right associative, meaning that `x ≤ y → y ≤ z → x ≤ z` means
exactly that `≤` is transitive.
"

/-- If $x \leq y$ and $y \leq z$, then $x \leq z$. -/
Statement le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  Hint "If you start with `rcases hxy with ⟨a, ha⟩` then `ha` will be a proof that `y = x + a`.
  If you want to instead *define* `y` to be `x + a` then you can do `rcases hxy with ⟨a, rfl⟩`.
  This is a time-saving trick. "
  rcases hxy with ⟨a, rfl⟩
  rcases hyz with ⟨b, rfl⟩
  use a + b
  exact add_assoc x a b

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
