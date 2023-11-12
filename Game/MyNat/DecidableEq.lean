import Game.MyNat.Addition-- makes simps work?
import Game.MyNat.PeanoAxioms
import Game.MyNat.Power -- just for tests
import Game.MyNat.LE
import Game.Levels.Algorithm.L07succ_ne_succ
import Mathlib.Tactic
namespace MyNat

@[MyNat_decide]
lemma ofNat_succ : (OfNat.ofNat (Nat.succ n) : ℕ) = MyNat.succ (OfNat.ofNat n) := _root_.rfl

macro "MyDecide" : tactic => `(tactic|(
  try simp only [MyNat_decide]
  try decide
))

instance instDecidableEq : DecidableEq MyNat
| 0, 0 => isTrue <| by
  show 0 = 0
  rfl
| succ m, 0 => isFalse <| by
  show succ m ≠ 0
  exact succ_ne_zero m
| 0, succ n => isFalse <| by
  show 0 ≠ succ n
  exact zero_ne_succ n
| succ m, succ n =>
  match instDecidableEq m n with
  | isTrue (h : m = n) => isTrue <| by
    show succ m = succ n
    rw [h]
    rfl
  | isFalse (h : m ≠ n) => isFalse <| by
    show succ m ≠ succ n
    exact succ_ne_succ m n h

example : 4 = 4 := by
  MyDecide

example : 4 ≠ 5 := by
  MyDecide

example : (0 : ℕ) + 0 = 0 := by
  MyDecide

example : (2 : ℕ) + 2 = 4 := by
  MyDecide

example : (2 : ℕ) + 2 ≠ 5 := by
  MyDecide

example : (20 : ℕ) + 20 = 40 := by
  MyDecide

example : (2 : ℕ) * 2 = 4 := by
  MyDecide

example : (2 : ℕ) * 2 ≠ 5 := by
  MyDecide

example : (3 : ℕ) ^ 2 ≠ 37 := by
  MyDecide
