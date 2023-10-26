import Mathlib.Tactic
import Lean

namespace Mathlib.Tactic
open Lean Meta Elab Tactic Term

elab "apply" t:term "at" i:ident : tactic => withMainContext do
  let fn ← Term.elabTerm t none
  let fnTp ← inferType fn
  let (ms, _, foutTp) ← forallMetaTelescopeReducing fnTp (some 1)
  unless ms.size == 1 do throwError "oops!"
  let finTp ← inferType ms[0]!
  let ldecl ← (← getLCtx).findFromUserName? i.getId
  let (mvs, outTp) ← show TacticM (Array Expr × Expr) from do
    let mut mvs := #[ms[0]!]
    let mut cmpTp := finTp
    let mut outTp := foutTp
    while !(← isDefEq cmpTp ldecl.type) do
      let (ms, _, newfoutTp) ← forallMetaTelescopeReducing outTp (some 1)
      unless ms.size == 1 do throwError "oops!"
      mvs := mvs ++ ms
      cmpTp ← inferType ms[0]!
      outTp := newfoutTp
    mvs := mvs.pop
    return (mvs, outTp)
  let mainGoal ← getMainGoal
  let mainGoal ← mainGoal.tryClear ldecl.fvarId
  let mainGoal ← mainGoal.assert ldecl.userName outTp (mkAppN fn (mvs.push ldecl.toExpr))
  let (_, mainGoal) ← mainGoal.intro1P
  replaceMainGoal <| [mainGoal] ++ mvs.toList.map fun e => e.mvarId!

example (A B C : Prop) (ha : A) (f : A → B) (g : B → C) : C := by
  apply f at ha -- ha : B
  apply g at ha
  exact ha

open Nat

example (a b : Nat) (h : succ a = succ b) : a = b := by
  let succ_inj2 (a b : Nat) : succ a = succ b → a = b := by simp
  apply succ_inj2 at h
  exact h

-- Test
example (A B C : Prop) (ha : A) (f : A → B) (g : B → C) : C := by
  apply f at ha
  apply g at ha
  exact ha

-- failing test
example (h1 : ∀ x, Nat.succ x = 4 → x = 3) (a : Nat) (h : Nat.succ a = 4) : a = 3 := by
  -- apply h1 at h -- fails
  replace h := h1 _ h -- works
  exact h
