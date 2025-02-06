import Game.MyNat.LE

namespace MyNat

def lt (a b : ℕ) :=  succ a ≤ b

-- notation
instance : LT MyNat := ⟨MyNat.lt⟩

theorem lt_iff_succ_le (a b : ℕ) : a < b ↔ succ a ≤ b := by rfl

end MyNat
