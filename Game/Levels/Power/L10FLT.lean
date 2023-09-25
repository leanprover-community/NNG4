import Game.Levels.Power.L09add_sq

World "Power"
Level 10
Title "Fermat's Last Theorem"

namespace MyNat

Introduction
"
Second stage!

We now have enough to state mathematically accurate, but slightly
clunky, version of Fermat's Last Theorem.

Fermat's Last Theorem states that if $x,y,z>0$ and $m>2$ then $x^m+y^m\not=z^m$.
If you didn't do inequality world yet then we can't talk about $m>2$,
so we have to resort to the hack of using `succ (succ (succ n))` for `m`,
which guarantees it's big enough. Similarly instead of `x > 0` we
use `succ a`.

This level looks superficially like other levels we have seen,
but the shortest solution known to humans would translate into
many millions of lines of Lean code. The author of this game,
Kevin Buzzard, is working on translating the proof by Wiles
and Taylor into Lean, although this task will take many years.
You can see the current state of his efforts at ...?

**TODO** add info if I get funded.
"

/-- For all naturals $a$ and $b$, we have
$$(a+b)^2=a^2+b^2+2ab.$$ -/
Statement
    (a b c n : ℕ) : (succ a) ^ (succ (succ (succ n))) + (succ b) ^ (succ (succ (succ n))) ≠ (succ c) ^ (succ (succ (succ n))) := by
  sorry

LemmaTab "Pow"

Conclusion
"
Congratulations! You proved Fermat's Last Theorem!
"
