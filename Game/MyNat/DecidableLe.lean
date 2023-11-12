import Game.MyNat.DecidableEq
import Game.Levels.LessOrEqual

namespace MyNat

instance instDecidableLe : DecidableRel (α := ℕ) (· ≤ ·)
| 0, _ => isTrue <| by
  show 0 ≤ _
  apply MyNat.zero_le
| succ m, 0 => isFalse <| by
  show ¬ succ m ≤ 0
  rintro ⟨a, ha⟩
  symm at ha
  apply eq_zero_of_add_right_eq_zero at ha
  apply succ_ne_zero at ha
  exact ha
| succ m, succ n =>
  match instDecidableLe m n with
  | isTrue (h : m ≤ n) => isTrue <| by
    show succ m ≤ succ n
    rcases h with ⟨a, rfl⟩
    use a
    rw [succ_add]
    rfl
  | isFalse (h : ¬ m ≤ n) => isFalse <| by
    show ¬ succ m ≤ succ n
    contrapose! h
    rcases h with ⟨a, ha⟩
    use a
    rw [succ_add] at ha
    apply succ_inj at ha
    exact ha

example : (20 : ℕ) ≤ 30 := by
  decide

example : ¬ ((30 : ℕ) ≤ 20) := by
  decide
