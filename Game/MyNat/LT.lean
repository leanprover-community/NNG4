import Game.MyNat.LE

namespace MyNat

def lt (a b : ℕ) :=  a ≤ b ∧ a ≠ b

-- notation
instance : LT MyNat := ⟨MyNat.lt⟩

end MyNat
