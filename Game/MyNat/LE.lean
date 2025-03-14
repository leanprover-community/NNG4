import Game.MyNat.Multiplication

namespace MyNat

def le (a b : ℕ) :=  ∃ (c : ℕ), b = a + c

/-

Another choice would have been to define `MyNat.le` recursively, like `Nat.le` is
defined in core:

```
protected inductive Nat.le (n : Nat) : Nat → Prop
  /-- Less-equal is reflexive: `n ≤ n` -/
  | refl     : Nat.le n n
  /-- If `n ≤ m`, then `n ≤ m + 1`. -/
  | step {m} : Nat.le n m → Nat.le n (succ m)
```

Yet another option would be the definition I tried in Exercise 9 of the 2017 prototype version
of the game (see https://xenaproject.wordpress.com/2017/10/31/building-the-non-negative-integers-from-scratch/).

I ultimately didn't choose these options because tests showed
that mathematicians found building the basic API a lot more confusing than
with the existence definition.
-/

-- notation
instance : LE MyNat := ⟨MyNat.le⟩

-- We don't use this any more; I tell the users `≤` is *notation*
-- theorem le_iff_exists_add (a b : ℕ) : a ≤ b ↔ ∃ (c : ℕ), b = a + c := Iff.rfl

end MyNat
