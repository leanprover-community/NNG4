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

require std from git
  "https://github.com/leanprover/std4" @ "44a92d84c31a88b9af9329a441890ad449d8cd5f"

package Game where
  moreLeanArgs := #["-Dtactic.hygienic=false"]
  moreServerArgs := #["-Dtactic.hygienic=false"]

@[default_target]
lean_lib Game
