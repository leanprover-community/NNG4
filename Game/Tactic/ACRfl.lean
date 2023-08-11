
import Lean

-- Note: to get `ac_rfl` working (which is in core), we just
-- need the two instances below in the files where
-- `add_assoc` and `add_comm` are proven.
-- This file is only for demonstration purpose.

import Game.Levels.Addition.Level_2 -- defines `MyNat.add_assoc`
import Game.Levels.Addition.Level_4 -- defines `MyNat.add_comm`

instance : Lean.IsAssociative (α := ℕ) (·+·) := ⟨MyNat.add_assoc⟩
instance : Lean.IsCommutative (α := ℕ) (·+·) := ⟨MyNat.add_comm⟩

example (a b c : ℕ) : c + (b + a) = (a + b) + c := by
  ac_rfl
