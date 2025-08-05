import Lake
open Lake DSL

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

def LocalGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := DependencySrc.path "../lean4game/server"
  version? := none
  opts := ∅
}

def RemoteGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := DependencySrc.git "https://github.com/leanprover-community/lean4game.git" leanVersion "server"
  version? := s!"git#{leanVersion}"
  opts := ∅
}

/- Choose GameServer dependency depending on the environment variable `LEAN4GAME`. -/
open Lean in
#eval (do
  let gameServerName := if get_config? lean4game.local |>.isSome then
    ``LocalGameServer else ``RemoteGameServer
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env gameServerName)
  : Elab.Command.CommandElabM Unit)

/-! # USER SECTION

Below are all the dependencies the game needs. Add or remove packages here as you need them.

Note: If your package (like `mathlib` or `Std`) has tags of the form `v4.X.0` then
you can use `require mathlib from git "[URL]" @ leanVersion`
 -/



require "leanprover-community" / mathlib @ s!"git#{leanVersion}"



/-! # END USER SECTION -/

-- NOTE: We abuse the `trace.debug` option to toggle messages in VSCode on and
-- off when calling `lake build`. Ideally there would be a better way using `logInfo` and
-- an option like `lean4game.verbose`.
package Game where
  moreLeanArgs := #[
    "-Dtactic.hygienic=false",
    "-Dlinter.unusedVariables.funArgs=false",
    "-Dweak.linter.unusedTactic=false",
    "-Dtrace.debug=false"]
  moreServerOptions := #[
    ⟨`tactic.hygienic, false⟩,
    ⟨`linter.unusedVariables.funArgs, true⟩,
    ⟨`weak.linter.unusedTactic, false⟩,
    ⟨`trace.debug, true⟩]
  weakLeanArgs := #[]

@[default_target]
lean_lib Game
