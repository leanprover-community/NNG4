import Lake
open Lake DSL

def LocalGameServer : Dependency := {
  name := `GameServer
  src := Source.path "../lean4game/server"
}

def RemoteGameServer : Dependency := {
  name := `GameServer
  src := Source.git "https://github.com/leanprover-community/lean4game.git" "main" "server"
}

/- Choose dependency depending on the environment variable NODE_ENV -/
open Lean in
#eval (do
  let gameServerName :=
    if (← IO.getEnv "NODE_ENV") == some "development" then ``LocalGameServer else ``RemoteGameServer
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env gameServerName)
   : Elab.Command.CommandElabM Unit)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.1.0"

-- NOTE: We abuse the `trace.debug` option to toggle messages in VSCode on and
-- off when calling `lake build`. Ideally there would be a better way using `logInfo` and
-- an option like `lean4game.verbose`.
package Game where
  moreLeanArgs := #["-Dtactic.hygienic=false", "-Dlinter.unusedVariables.funArgs=false",
    "-Dtrace.debug=false"]
  moreServerArgs := #["-Dtactic.hygienic=false", "-Dlinter.unusedVariables.funArgs=true",
    "-Dtrace.debug=true"]
  weakLeanArgs := #[]

@[default_target]
lean_lib Game
