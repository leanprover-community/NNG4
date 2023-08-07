import Game.Levels.Addition.L01two_add_one
import Game.Levels.Addition.L02one_add_one
import Game.Levels.Addition.L03two_add_two
import Game.Levels.Addition.L04decide
import Game.Levels.Addition.L05zero_add
import Game.Levels.Addition.L06succ_add
import Game.Levels.Addition.L07add_comm
import Game.Levels.Addition.L08add_assoc
import Game.Levels.Addition.L09add_left_comm
import Game.Levels.Addition.L10annoying
import Game.Levels.Addition.L11ac_rfl


World "Addition"
Title "Addition World"

Introduction
"
Welcome to Addition World. If you've done all four levels in tutorial world
and know about `rw` and `rfl`, then you're in the right place. Here's
a reminder of the things you're now equipped with which we'll need in this world.

## Data:

  * a type called `ℕ` or `MyNat`.
  * a term `0 : ℕ`, interpreted as the number zero.
  * a function `succ : ℕ → ℕ`, with `succ n` interpreted as \"the number after `n`\".
  * Usual numerical notation `0,1,2` etc. (although `2` onwards will be of no use to us until much later ;-) ).
  * Addition (with notation `a + b`).

## Theorems:

  * `add_zero (a : ℕ) : a + 0 = a`. Use with `rw [add_zero]`.
  * `add_succ (a b : ℕ) : a + succ(b) = succ(a + b)`. Use with `rw [add_succ]`.
  * The principle of mathematical induction. Use with `induction` (which we learn about in this chapter).


## Tactics:

  * `rfl` :  proves goals of the form `X = X`.
  * `rw [h]` : if `h` is a proof of `A = B`, changes all `A`'s in the goal to `B`'s.
  * `induction n with d hd` : we're going to learn this right now.


You will also find all this information in your Inventory on the right hand side of the screen.
Be sure to click around so that you know which tools you have available to you
at any time.
"
