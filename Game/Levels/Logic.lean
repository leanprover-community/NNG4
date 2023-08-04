import Game.Levels.Logic.bonus_peano_axiom_levels

World "Logic"
Title "Logic World"

Introduction
"
All the axioms for commutative semirings like `ℕ` are *equalities*.
They say things like `∀ a b c, a * (b + c) = a * b + a * c`.
Induction and rewriting will take you there.

You will never need Peano's last two axioms, which were
that `0 ≠ succ a` and `succ a = succ b → a = b` (injectivity of `succ`).
We introduce (and even prove!) these axioms here.

Do you even need addition world to do this?
"
