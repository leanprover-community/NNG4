import Lake
open Lake DSL

def LocalGameServer : Dependency := {
  name := `GameServer
  src := Source.path "../lean4game/server"
}

def RemoteGameServer : Dependency := {
  name := `GameServer
  src := Source.git "https://github.com/leanprover-community/lean4game.git" "a423681150d88e06ae9bda9bb056b8faf83251cb" "server"
}

/- Choose dependency depending on the environment variable NODE_ENV -/
open Lean in
#eval (do
  let gameServerName :=
    if (← IO.getEnv "NODE_ENV") == some "development" then ``LocalGameServer else ``RemoteGameServer
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env gameServerName)
   : Elab.Command.CommandElabM Unit)

-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4" @ "88e129706828e01b7622d6635af1ca6667e25bac"

-- `Game` fix:
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "7d308680dc444730e84a86c72357ad9a7aea9c4b"



package Game where
  moreLeanArgs := #["-Dtactic.hygienic=false", "--quiet"]
  moreServerArgs := #["-Dtactic.hygienic=false", "--quiet"]
  weakLeanArgs := #["--quiet"]

@[default_target]
lean_lib Game
