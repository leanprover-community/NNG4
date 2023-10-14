import Game.MyNat.Definition
import Mathlib.Tactic.Cases

/-!
# Modified `cases` tactic

Modify `cases` tactic to always show `(0 : MyNat)` instead of `MyNat.zero` and
to support the lean3-style `with` keyword.

This is mainly copied and modified from the mathlib-tactic `cases'`.
-/

namespace MyNat

/-- Modified `casesOn` principal to use `0` instead of `MyNat.zero`. -/
def casesOn' {P : ℕ → Sort u} (t : ℕ) (zero : P 0)
    (succ : (a : ℕ) → P (MyNat.succ a)) : P t := by
  cases t with
  | zero => assumption
  | succ n =>
    apply succ

open Lean Meta Elab Parser Tactic Mathlib.Tactic
open private getElimNameInfo from Lean.Elab.Tactic.Induction

/-- Modified `cases` tactic for this game.

Usage: `cases n with d` if `n : ℕ`; `cases h with h1 h2` if `h : P ∨ Q`; `cases h with c hc` if `h : a ≤ b`.

*(This implementation mimics the `cases'` from mathlib. The actual `cases` tactic in mathlib has a more complex syntax)*
-/
elab (name := cases) "cases " tgts:(Parser.Tactic.casesTarget,+) usingArg:((" using " ident)?)
    withArg:((" with" (ppSpace colGt binderIdent)+)?) : tactic => do
  let targets ← elabCasesTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimNameInfo usingArg targets (induction := false)

    -- Edit: If `elimInfo.name` is `MyNat.casesOn` we want to use `MyNat.rec'` instead.
    -- TODO: This seems extremely hacky. Especially that we need to get the `elimInfo` twice.
    -- Please improve this.
    let elimInfo ← match elimInfo.name with
    | `MyNat.casesOn =>
      let modifiedUsingArgs : TSyntax Name.anonymous := ⟨
        match usingArg.raw with
        | .node info kind #[] =>
          -- TODO: How do you construct syntax in a semi-userfriendly way??
          .node info kind #[.atom info "using", .ident info "MyNat.rec'".toSubstring `MyNat.casesOn' []]
        | other => other ⟩
      let newElimInfo ← getElimNameInfo modifiedUsingArgs targets (induction := false)
      pure newElimInfo
    | _ => pure elimInfo

    let targets ← addImplicitTargets elimInfo targets
    let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM (instantiateMVars elimArgs[·]!)
    let motive := elimArgs[elimInfo.motivePos]!
    let g ← generalizeTargetsEq g (← inferType motive) targets
    let (targetsNew, g) ← g.introN targets.size
    g.withContext do
      ElimApp.setMotiveArg g motive.mvarId! targetsNew
      g.assign result.elimApp
      let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
         (numEqs := targets.size) (toClear := targetsNew)
      setGoals <| subgoals.toList ++ gs

end MyNat
