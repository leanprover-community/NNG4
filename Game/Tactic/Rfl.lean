import Lean.Meta.Tactic.Refl
import Lean.Elab.Tactic.Basic

/-! # `rfl` tactic

Added `withReducible` to prevent `rfl` proving stuff like `n + 0 = n`.
-/

open Lean Meta Elab Tactic

/--
Close given goal using `Iff.refl`.
-/
def Lean.MVarId.iffRefl (mvarId : MVarId) : MetaM Unit := do
  mvarId.withContext do
    mvarId.checkNotAssigned `iffRefl
    let targetType ← mvarId.getType'
    let some (lhs, rhs) := Expr.app2? targetType ``Iff
      | throwTacticEx `iffRefl mvarId m!"iff expected"
    unless ← isDefEq lhs rhs do
      throwTacticEx `iffRefl mvarId
        m!"lhs{indentD lhs}\nis not definitionally equal to rhs{indentD rhs}"
    mvarId.assign (.app (mkConst ``Iff.refl) lhs)

namespace MyNat

-- @[match_pattern] def MyNat.rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

/-- Modified `rfl` tactic.

`rfl` closes goals of the form `A = A`.

Note that the version for this game is somewhat weaker than the real one. -/
syntax (name := rfl) "rfl" : tactic

@[tactic MyNat.rfl] def evalRfl : Tactic := fun _ =>
  liftMetaTactic fun mvarId => withReducible do
    let targetType ← mvarId.getType'
    match targetType.getAppFn with
      | .const ``Eq .. => mvarId.refl
      | .const ``Iff .. => mvarId.iffRefl
      | _ => throwTacticEx `rfl mvarId "expecting an equality or iff"
    pure []

-- @[tactic MyNat.rfl] def evalRfl : Tactic := fun _ =>
--   liftMetaTactic fun mvarId => do mvarId.refl; pure []
-- (with_reducible rfl)

end MyNat
