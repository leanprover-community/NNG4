import Mathlib.Init.Core
import Game.MyNat.Definition
import Game.MyNat.Division
import Game.MyNat.LE

namespace MyNat

def Prime (n : ℕ) := (2 ≤ n) ∧ ∀ (a : ℕ), a ∣ n → a = 1 ∨ a = n

end MyNat
