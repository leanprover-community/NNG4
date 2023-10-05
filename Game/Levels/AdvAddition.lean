import Game.Levels.Addition
import Game.MyNat.AdvAddition -- `zero_ne_succ` and `succ_inj`
import Game.Levels.AdvAddition.L01assumption
import Game.Levels.AdvAddition.L02more_assumption
import Game.Levels.AdvAddition.L03apply
import Game.Levels.AdvAddition.L04succ_inj1
import Game.Levels.AdvAddition.L05succ_inj2
import Game.Levels.AdvAddition.L06intro

World "AdvAddition"
Title "Advanced Addition World"

Introduction
"
In Advanced Addition World we'll learn the `apply` tactic,
and several other tactics, enabling us to argue both forwards
and backwards.

We'll use this technique to prove that $2+2\\neq5$
and much more.

Click on \"Start\" to proceed.
"
