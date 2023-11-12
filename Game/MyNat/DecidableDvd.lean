import Game.MyNat.DecidableLe
import Game.Levels.LessOrEqual
import Game.Levels.Multiplication

-- NOTE: this probably needs a whole new "advanced algorithm world"
-- where we develop a theory of a % b computably, and show that for b > 0,
-- b ∣ a ↔ a % b = 0 (and hence it's decidable)

namespace MyNat

instance : Dvd MyNat where
  dvd a b := ∃ c, a * c = b

instance instDecidableDvd : DecidableRel (α := ℕ) (· ∣ ·)
| 0, 0 => isTrue <| by
  show _ ∣ 0
  use 0
  rw [mul_zero]
  rfl
| 0, succ m => isFalse <| by
  rintro ⟨a, ha⟩
  rw [zero_mul] at ha
  apply zero_ne_succ at ha
  exact ha
| succ m, n =>
  show Decidable (succ m ∣ n) by
  -- idea : just show m ∣ n iff n % m = 0 and show that n % m is computable
  sorry

-- *TODO* uncomment when working
-- example : (2 : ℕ) ∣ 4 := by MyDecide
