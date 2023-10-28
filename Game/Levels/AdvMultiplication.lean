import Game.Levels.AdvMultiplication.L01mul_le_mul_right

World "AdvMultiplication"
Title "Advanced Multiplication World"

Introduction
"
Advanced *Addition* World proved various implications
involving addition, such as `x + y = 0 → x = 0` and `x + y = x → y = 0`.
These lemmas were used to prove basic facts about ≤ in ≤ World.

In Advanced Multiplication World we prove analogous
facts about multiplication, such as `x * y = 1 → x = 1`, and
`x * y = x → y = 1` (assuming `x ≠ 0` in the latter result). This will prepare
us for Divisibility World.

Multiplication World is more complex than Addition World. In the same
way, Advanced Multiplication world is more complex than Advanced Addition
World. One reason for this is that certain intermediate results are only
true under the additional hypothesis that one of the variables is non-zero.
This causes some unexpected extra twists.
"
