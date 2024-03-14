import Game.MyNat.PeanoAxioms
import Game.Levels.Algorithm.L07succ_ne_succ -- succ_ne_succ
import Game.Tactic.Decide -- modified decide tactic

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
