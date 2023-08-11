import Lake
open Lake DSL

def LocalGameServer : Dependency := {
  name := `GameServer
  src := Source.path "../lean4game/server"
}

def RemoteGameServer : Dependency := {
  name := `GameServer
  src := Source.git "https://github.com/leanprover-community/lean4game.git" "adb93e30bd0c0364a91b7ee4c606a01d33c5acd4" "server"
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
  "https://github.com/leanprover-community/mathlib4" @ "b04c509ef69fc7939b5f67715a635e15743dbe3c"



package Game where
  moreLeanArgs := #["-Dtactic.hygienic=false"]
  moreServerArgs := #["-Dtactic.hygienic=false"]

@[default_target]
lean_lib Game
