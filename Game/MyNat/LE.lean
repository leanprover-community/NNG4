import Game.MyNat.Multiplication
import Mathlib.Tactic

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

--@[leakage] theorem le_def' : MyNat.le = (≤) := rfl

theorem le_iff_exists_add (a b : ℕ) : a ≤ b ↔ ∃ (c : ℕ), b = a + c := Iff.rfl

example (a b : Nat) : a ≤ b ↔ ∃ c, b = a + c := by exact _root_.le_iff_exists_add

@[MyNat_decide]
theorem toNat_le (m n : MyNat) : m ≤ n ↔ m.toNat ≤ n.toNat :=
⟨ fun ⟨a, ha⟩ ↦ _root_.le_iff_exists_add.2 ⟨toNat a, by simp [ha, MyNat_decide]⟩,
  by
    intro h
    rw [_root_.le_iff_exists_add] at h
    cases' h with c hc
    use ofNat c
    simp [MyNat_decide, hc]⟩

--  induction n <;> simp [MyNat_decide, *, Nat.pow_zero, Nat.pow_succ];

end MyNat
