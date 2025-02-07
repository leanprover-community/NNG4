import Game.MyNat.PeanoAxioms
import Game.MyNat.Addition
import Game.Levels.Implication
import Game.Tactic.Decide
import Game.Levels.Algorithm

namespace MyNat

def le (a b : ℕ) :=  ∃ (c : ℕ), b = a + c

-- Another choice is to define it recursively:
-- (kb) note: I didn't choose this option because tests showed
-- that mathematicians found it a lot more confusing than
-- the existence definition.

-- | le 0 _
-- | le (succ a) (succ b) = le ab

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
