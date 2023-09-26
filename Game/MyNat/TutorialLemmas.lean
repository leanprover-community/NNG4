import Game.MyNat.Addition
/-
This file adds proofs of results which were used in Tutorial World but
which we can't import (because tutorial world imports multiplication
in the first level, and we don't want to import this too early)
-/

namespace MyNat

theorem one_eq_succ_zero : 1 = succ 0 := by rfl
theorem two_eq_succ_one : 2 = succ 1 := by rfl
theorem three_eq_succ_two : 3 = succ 2 := by rfl
theorem four_eq_succ_three : 4 = succ 3 := by rfl
