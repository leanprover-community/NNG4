import Lean.Meta.Tactic.Assumption
import Lean.Elab.Tactic.Basic

/-! # `assumption` tactic

Added `withReducible` so that `assumption` ignores definitional equality.
-/

namespace MyNat

open Lean Meta Elab Tactic

syntax (name := assumption) "assumption" : tactic

@[tactic MyNat.assumption] def evalAssumption : Tactic := fun _ =>
  liftMetaTactic fun mvarId => do withReducible <| mvarId.assumption; pure []

end MyNat
