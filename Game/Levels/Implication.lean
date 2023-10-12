import Game.Levels.Implication.L01exact
import Game.Levels.Implication.L02exact2
import Game.Levels.Implication.L03apply
import Game.Levels.Implication.L04succ_inj
import Game.Levels.Implication.L05succ_inj2
import Game.Levels.Implication.L06intro
import Game.Levels.Implication.L07intro2
import Game.Levels.Implication.L08ne
import Game.Levels.Implication.L09zero_ne_succ
import Game.Levels.Implication.L10one_ne_zero
import Game.Levels.Implication.L11two_add_two_ne_five

World "Implication"
Title "Implication World"

Introduction
"
We've proved that $2+2=4$; in Implication World we'll learn
how to prove $2+2\\neq 5$.

In Addition World we proved *equalities* like `x + y = y + x`.
In this second tutorial world we'll learn some new tactics,
enabling us to prove *implications*
like $x+1=4 \\implies x=3.

We'll also learn two new fundamental facts about
natural numbers, which Peano introduced as axioms.

Click on \"Start\" to proceed.
"
