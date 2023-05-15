/- Copied from mathlb. -/
import Lean

namespace Game.Tactic.LeftRight
open Lean Meta Elab Tactic
def leftRightMeta (name : Name) (idx max : Nat) (goal : MVarId) : MetaM (List MVarId) := do
  goal.withContext do
    goal.checkNotAssigned name
    let target ←  goal.getType'
    matchConstInduct target.getAppFn
      (fun _ ↦ throwTacticEx `constructor goal "target is not an inductive datatype")
      fun ival us ↦ do
        unless ival.ctors.length == max do
          throwTacticEx `constructor goal
            s!"{name} target applies for inductive types with exactly two constructors"
        let ctor := ival.ctors[idx]!
        goal.apply <| mkConst ctor us

end LeftRight

open LeftRight

elab "left" : tactic => do
  Lean.Elab.Tactic.liftMetaTactic (leftRightMeta `left 0 2)

elab "right" : tactic => do
  Lean.Elab.Tactic.liftMetaTactic (leftRightMeta `right 1 2)
