import Game.Levels.Addition
import Game.MyNat.AdvAddition -- `zero_ne_succ` and `succ_inj`
import Game.Levels.AdvAddition.L01assumption
import Game.Levels.AdvAddition.L02assumption2
import Game.Levels.AdvAddition.L03apply
import Game.Levels.AdvAddition.L04succ_inj
import Game.Levels.AdvAddition.L05succ_inj2
import Game.Levels.AdvAddition.L06intro
import Game.Levels.AdvAddition.L07intro2
import Game.Levels.AdvAddition.L08add_right_cancel
import Game.Levels.AdvAddition.L09add_left_cancel
import Game.Levels.AdvAddition.L10add_left_eq_self
import Game.Levels.AdvAddition.L11add_right_eq_self


World "AdvAddition"
Title "Advanced Addition World"

Introduction
"
We've proved that $2+2=4$; in Advanced Addition World we'll learn
how to prove that $2+2\\neq 5$.

In Addition World we proved *equalities* like `x + y = y + x`.
In this world we'll learn how to prove *implications*
like $x+n=y+n \\implies x=y$. We'll have to learn three new
tactics to do this: `assumption`, `apply` and `intro`.
We'll also learn two new fundamental facts about
natural numbers, which Peano introduced as axioms.

Click on \"Start\" to proceed.
"
