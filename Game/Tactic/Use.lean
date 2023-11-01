import Mathlib.Tactic.Use

/-!
Defines the `use` tactic.

## Implementation notes

This simply calls `use` from Mathlib with no discharger.
-/

open Lean Elab Tactic Mathlib.Tactic

/-- For goals of the form `∃ (n : ℕ), P n` the tactic `use` can be used to provide a `n` which
will satisfy `P n`. For multiple constructors like `∃ (n m : ℕ), P n`, you can provide
comma-separated values: `use 2, 3`.

Note that the version for this game is somewhat weaker than the real one. For example,
`use` in Mathlib
automatically tries to apply `rfl` afterwards.
-/
-- @[inherit_doc Mathlib.Tactic.useSyntax]
elab (name := MyNat.useSyntax) "use" ppSpace args:term,+ : tactic => do
  -- use Mathlib's `use` without any discharger
  let discharger := evalTactic (← `(tactic|skip))
  runUse false discharger args.getElems.toList
