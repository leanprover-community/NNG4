import Game.MyNat.Definition
import Game.MyNat.Multiplication

namespace MyNat


def dvd (a b : ℕ) :=  ∃ (c : ℕ), b = a * c

instance : Dvd MyNat := ⟨MyNat.dvd⟩

theorem dvd_iff_exists_mul (a b : ℕ) : a ∣ b ↔ ∃ (c : ℕ), b = a * c := Iff.rfl

end MyNat
