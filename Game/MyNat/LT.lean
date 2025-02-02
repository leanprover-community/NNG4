import Game.MyNat.LE

namespace MyNat

def lt (a b : ℕ) :=  a.succ ≤ b

-- notation
instance : LT MyNat := ⟨MyNat.lt⟩

theorem lt_iff_succ_le (a b : ℕ) : a < b ↔ a.succ ≤ b := by rfl

end MyNat
