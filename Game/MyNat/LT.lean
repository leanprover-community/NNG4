import Game.MyNat.LE

namespace MyNat

def lt (a b : ℕ) :=  succ a ≤ b

-- notation
instance : LT MyNat := ⟨MyNat.lt⟩

instance instDecLT : DecidableRel ( (· < · ) : ℕ → ℕ → Prop)
| a, b => instDecLE (succ a) b

theorem lt_iff_succ_le (a b : ℕ) : a < b ↔ succ a ≤ b :=
  Iff.intro id id
  --sometimes by rfl works.  Now it doesn't.  I don't understand it.

-- def min (a b : ℕ) := ite (a ≤ b) a b
-- def max (a b : ℕ) := ite (b ≤ a) a b

end MyNat
