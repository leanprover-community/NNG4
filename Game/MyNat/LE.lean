import Game.MyNat.PeanoAxioms
import Game.MyNat.Addition
import Game.Levels.Implication
import Game.Tactic.Decide
import Game.Levels.Algorithm

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

instance instDecLE : DecidableRel ( (· ≤ · ) : ℕ → ℕ → Prop )
| 0, l => isTrue <| by
  use l
  rw [zero_add l]
  rfl
| succ m, 0 => isFalse <| by
  rintro ⟨n,hn⟩
  rw [succ_add] at hn
  have h1 := succ_ne_zero (m + n)
  exact h1 hn.symm
| succ m, succ n =>
  match instDecLE m n with
  | isTrue (h : m ≤ n) => isTrue <| by
    cases h with k hk
    use k
    rw [succ_add]
    rw [hk]
    rfl
  | isFalse (h : ¬(m ≤ n))  => isFalse <| by
    intro h0
    apply h
    cases h0 with k hk
    rw [succ_add] at hk
    have h1 := succ_inj n (m + k) hk
    use k
    exact h1







-- We don't use this any more; I tell the users `≤` is *notation*
-- theorem le_iff_exists_add (a b : ℕ) : a ≤ b ↔ ∃ (c : ℕ), b = a + c := Iff.rfl

end MyNat
