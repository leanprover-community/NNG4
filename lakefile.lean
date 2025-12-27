import Lake
open Lake DSL

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

/--
Use the GameServer from a `lean4game` folder lying next to the game on your local computer.
Activated with `lake update -Klean4game.local`.
-/
def LocalGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := DependencySrc.path "../lean4game/server"
  version? := none
  opts := ∅
}

/--
Use the GameServer version from github.
Deactivate local version with `lake update -R`.
-/
def RemoteGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := DependencySrc.git "https://github.com/leanprover-community/lean4game.git" "main" "server"
  version? := s!"git#{leanVersion}"
  opts := ∅
}

/-
Choose GameServer dependency depending on whether `-Klean4game.local` has been passed to `lake`.
-/
open Lean in
#eval (do
  let gameServerName := if get_config? lean4game.local |>.isSome then
    ``LocalGameServer else ``RemoteGameServer
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env gameServerName)
  : Elab.Command.CommandElabM Unit)

/-!
# USER DEPENDENCIES

Add any further dependencies of your game below.

Note: If your package (like `mathlib` or `Std`) has tags of the form `v4.X.0` then
you can use

```
require "leanprover-community" / mathlib @ git leanVersion
```
 -/

require "leanprover-community" / mathlib @ git leanVersion

/-!
# PACKAGE CONFIGURATION

Here you can set options used in your game. The player will use the same options as you'll
have set here.

NOTE: The `leanOptions` and `moreServerOptions` influence how the player preceives the game.
For example, it is important to have `linter.all` set to `false` to prevent any linter
warnings from showing up during playing.

NOTE: We abuse the `trace.debug` option to toggle messages in VSCode on and
off when calling `lake build`. Ideally there would be a better way using `logInfo` and
an option like `lean4game.verbose`.
-/
package Game where
  /- Used in all cases. -/
  leanOptions := #[
    /- linter warnings might block the player. (IMPORTANT) -/
    ⟨`linter.all, false⟩,
    /- make all assumptions always accessible. -/
    ⟨`tactic.hygienic, false⟩]
  /- Used when calling `lake build`. -/
  moreLeanArgs := #[
    -- TODO: replace with `lean4game.verbose`
    "-Dtrace.debug=false"]
  /- Used when opening a file in VSCode or when playing the game. -/
  moreServerOptions := #[
    -- TODO: replace with `lean4game.verbose`
    ⟨`trace.debug, true⟩]

@[default_target]
lean_lib Game
