import Game.MyNat.Addition-- makes simps work?
import Game.MyNat.PeanoAxioms
import Game.MyNat.Power -- just for tests
import Game.MyNat.LE
import Game.Levels.Algorithm.L07succ_ne_succ
import Mathlib.Tactic
namespace MyNat

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
  try simp only [MyNat_decide]
  try decide

example : 4 ≠ 5 := by
  try simp only [MyNat_decide]
  try decide

example : (0 : ℕ) + 0 = 0 := by
  try simp only [MyNat_decide]
  try decide

example : (2 : ℕ) + 2 = 4 := by
  try simp only [MyNat_decide]
  try decide

example : (2 : ℕ) + 2 ≠ 5 := by
  try simp only [MyNat_decide]
  try decide

example : (20 : ℕ) + 20 = 40 := by
  try simp only [MyNat_decide]
  try decide

example : (2 : ℕ) * 2 = 4 := by
  try simp only [MyNat_decide]
  try decide

example : (2 : ℕ) * 2 ≠ 5 := by
  try simp only [MyNat_decide]
  try decide

example : (3 : ℕ) ^ 2 ≠ 37 := by
  try simp only [MyNat_decide]
  try decide

example : (2 : ℕ) ≤ 3 := by
  try simp only [MyNat_decide]
  try decide

-- **TODO** uncomment test when Divisibility World hits
-- example : (2 : ℕ) ∣ 4 := by
--   try simp only [MyNat_decide]
--   try decide
