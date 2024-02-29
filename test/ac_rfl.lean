import Game.Levels.Addition.L03add_comm -- defines `MyNat.add_assoc`
import Game.Levels.Addition.L04add_assoc -- defines `MyNat.add_comm`

-- `ac_rfl` is defined in core. The two levels above add the instances
-- `Std.Commutative` and `Std.Associative` which are needed to make `ac_rfl` work.

example (a b c : MyNat) : a + (b + c) = (a + b) + c := by
  ac_rfl

example (a b c : MyNat) : a + (b + c) = (c + a) + b := by
  ac_rfl
