import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Induction
import Batteries.Tactic.OpenPrivate
import Batteries.Data.List.Basic
import Game.MyNat.Definition
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Cases

namespace MyNat

/-!
# Modified `induction` tactic

Modify `induction` tactic to always show `(0 : MyNat)` instead of `MyNat.zero` and
to support the lean3-style `with` keyword.

This is mainly copied and modified from the mathlib-tactic `induction'`.
-/

/--
Custom induction principial for the tactics `induction`.
Used to show `0` instead of `MyNat.zero` in the base case.
-/
def rec' {P : ℕ → Prop} (zero : P 0)
    (succ : (n : ℕ) → (n_ih : P n) → P (succ n)) (t : ℕ) : P t := by
  induction t with
  | zero => assumption
  | succ n =>
    apply succ
    assumption

end MyNat

open Lean Parser Tactic
open Meta Elab Elab.Tactic
open Mathlib.Tactic

open private getElimNameInfo generalizeTargets generalizeVars from Lean.Elab.Tactic.Induction

/--
Modified `induction` tactic for this game.

Usage: `induction n with d hd`.

*(The actual `induction` tactic has a more complex `with`-argument that works differently)*
-/
elab (name := MyNat.induction) "induction " tgts:(Parser.Tactic.elimTarget,+)
    usingArg:((" using " ident)?)
    withArg:((" with" (ppSpace colGt binderIdent)+)?)
    genArg:((" generalizing" (ppSpace colGt ident)+)?) : tactic => do
  let (targets, toTag) ← elabElimTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimNameInfo usingArg targets (induction := true)

    -- Edit: If `MyNat.rec` is used, we want to use `MyNat.rec'` instead.
    let elimInfo ← match elimInfo.elimExpr.getAppFn.constName? with
    | some `MyNat.rec =>
      let modifiedUsingArgs : TSyntax Name.anonymous := ⟨
        match usingArg.raw with
        | .node info kind #[] =>
          -- TODO: How do you construct syntax in a semi-userfriendly way??
          .node info kind #[.atom info "using", .ident info "MyNat.rec'".toSubstring `MyNat.rec' []]
        | other => other ⟩
      let newElimInfo ← getElimNameInfo modifiedUsingArgs targets (induction := false)
      pure newElimInfo
    | _ => pure elimInfo

    let targets ← addImplicitTargets elimInfo targets
    checkInductionTargets targets
    let targetFVarIds := targets.map (·.fvarId!)
    g.withContext do
      let genArgs ← if genArg.1.isNone then pure #[] else getFVarIds genArg.1[1].getArgs
      let forbidden ← mkGeneralizationForbiddenSet targets
      let mut s ← getFVarSetToGeneralize targets forbidden
      for v in genArgs do
        if forbidden.contains v then
          throwError "variable cannot be generalized \
            because target depends on it{indentExpr (mkFVar v)}"
        if s.contains v then
          throwError "unnecessary 'generalizing' argument, \
            variable '{mkFVar v}' is generalized automatically"
        s := s.insert v
      let (fvarIds, g) ← g.revert (← sortFVarIds s.toArray)
      g.withContext do
        let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
        let elimArgs := result.elimApp.getAppArgs
        ElimApp.setMotiveArg g elimArgs[elimInfo.motivePos]!.mvarId! targetFVarIds
        g.assign result.elimApp
        let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
          (generalized := fvarIds) (toClear := targetFVarIds) (toTag := toTag)
        setGoals <| (subgoals ++ result.others).toList ++ gs
