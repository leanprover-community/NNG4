import Game.MyNat.Multiplication

namespace MyNat

def lt (a b : ℕ) :=  ∃ c : ℕ, a + succ c = b



-- notation
instance : LT MyNat := ⟨MyNat.lt⟩

end MyNat
