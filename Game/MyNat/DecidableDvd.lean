import Game.MyNat.DecidableLe
import Game.Levels.LessOrEqual
import Game.Levels.Multiplication

namespace MyNat

instance : Dvd MyNat where
  dvd a b := ∃ c, a * c = b

instance instDecidableDvd : DecidableRel (α := ℕ) (· ∣ ·)
| _, 0 => isTrue <| by
  show _ ∣ 0
  use 0
  rw [mul_zero]
  rfl
| 0, succ m => isFalse <| by
  rintro ⟨a, ha⟩
  rw [zero_mul] at ha
  apply zero_ne_succ at ha
  exact ha
| succ m, succ n =>
  show Decidable (succ m ∣ succ n) by
  -- idea : just show m ∣ n iff n % m = 0 and show that n % m is computable
  sorry

example : (2 : ℕ) ≤ 3 := by
  MyDecide

example : ¬ ((30 : ℕ) ≤ 20) := by
  MyDecide
