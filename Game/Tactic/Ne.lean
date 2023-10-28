import Lean

/-!
A pretty-printer that displays `¬ (a = b)` as `a ≠ b`.
-/

open Lean PrettyPrinter Delaborator SubExpr

@[delab app.Not] def delab_not_mem :=
  whenPPOption Lean.getPPNotation do
  let #[f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.getAppFn matches .const `Eq _ do failure
  let stx₁ ← SubExpr.withAppArg <| SubExpr.withNaryArg 1 delab
  let stx₂ ← SubExpr.withAppArg <| SubExpr.withNaryArg 2 delab
  return ← `($stx₁ ≠ $stx₂)
