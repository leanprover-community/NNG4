import Game.Levels.Multiplication.L01mul_one
import Game.Levels.Multiplication.L02zero_mul
import Game.Levels.Multiplication.L03succ_mul
import Game.Levels.Multiplication.L04mul_comm
import Game.Levels.Multiplication.L05one_mul
import Game.Levels.Multiplication.L06two_mul
import Game.Levels.Multiplication.L07mul_add
import Game.Levels.Multiplication.L08add_mul
import Game.Levels.Multiplication.L09mul_assoc


World "Multiplication"
Title "Multiplication World"

Introduction
" How should we define `37 * x`? Just like addition, we need to give definitions
when $x=0$ and when $x$ is a successor.

The zero case is easy: we define `37 * 0` to be `0`. Now say we know
`37 * d`. What should `37 * succ d` be? Well, that's $d+1$ $37$s,
it should be `37 * d + 37`.

Here are the definitions in Lean.

  * `mul_zero a : a * 0 = 0`
  * `mul_succ a d : a * succ d = a * d + a`

In this world, we must not only prove facts about multiplication like `a * b = b * a`,
we must also prove facts about how multiplication interacts with addition, like `a * (b + c) = a * b + a * c`.
Let's get started.
"
