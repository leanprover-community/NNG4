import Lake
open Lake DSL

def LocalGameServer : Dependency := {
  name := `GameServer
  src := Source.path "../lean4game/server"
}

def RemoteGameServer : Dependency := {
  name := `GameServer
  src := Source.git "https://github.com/leanprover-community/lean4game.git" "6437013479f57d442d55216fe2e69e9b6644c147" "server"
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
  "https://github.com/leanprover-community/mathlib4" @ "658235826386f03bfb2b231fa42ead956567ce60"



package Game where
  moreLeanArgs := #["-Dtactic.hygienic=false", "--quiet"]
  moreServerArgs := #["-Dtactic.hygienic=false", "--quiet"]
  weakLeanArgs := #["--quiet"]

@[default_target]
lean_lib Game
