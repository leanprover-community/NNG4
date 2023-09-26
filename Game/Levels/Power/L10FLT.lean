import Game.Levels.Power.L09add_sq

World "Power"
Level 10
Title "Fermat's Last Theorem"

namespace MyNat

Introduction
"
We now have enough to state mathematically accurate, but slightly
clunky, version of Fermat's Last Theorem.

Fermat's Last Theorem states that if $x,y,z>0$ and $m \\geq 3$ then $x^m+y^m\\not =z^m$.
If you didn't do inequality world yet then we can't talk about $m \\geq 3$,
so we have to resort to the hack of using `n + 3` for `m`,
which guarantees it's big enough. Similarly instead of `x > 0` we
use `a + 1`.

This level looks superficially like other levels we have seen,
but the shortest solution known to humans would translate into
many millions of lines of Lean code. The author of this game,
Kevin Buzzard, is working on translating the proof by Wiles
and Taylor into Lean, although this task will take many years.
You can see the current state of his efforts at ...?

**TODO** add info if I get funded.

## CONGRATULATIONS!

You've finished the main quest of the natural number game!
If you would like to learn more about how to use Lean to
prove theorems in mathematics, then **TODO** put link to
Mathematics In Lean when I'm not in the eurotunnel.
"

/-- For all naturals $a$ $b$ $c$ and $n$, we have
$$(a+1)^{n+3}+(b+1)^{n+3}\not=(c+1)^{n+3}.$$ -/
Statement
    (a b c n : ℕ) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
  sorry

LemmaTab "Pow"

Conclusion
"
Congratulations! You have proved Fermat's Last Theorem!
"
