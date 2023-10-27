import Game.Levels.Multiplication
import Game.MyNat.Power


World "Power"
Level 1
Title "zero_pow_zero"

namespace MyNat

Introduction "Mathematicians sometimes debate what `0 ^ 0` is;
the answer depends, of course, on your definitions. In this
game, `0 ^ 0 = 1`. See if you can prove it.

Check out the *Pow* tab in your list of theorems
to see the new proofs which are available."

DefinitionDoc Pow as "^" "
  `Pow a b`, with notation `a ^ b`, is the usual
  exponentiation of natural numbers. Internally it is
  defined via two axioms:

  * `pow_zero a : a ^ 0 = 1`

  * `pow_succ a b : a ^ succ b = a ^ b * a`

Note in particular that `0 ^ 0 = 1`.
"

NewDefinition Pow

LemmaDoc MyNat.pow_zero as "pow_zero" in "^" "
`pow_zero a : a ^ 0 = 1` is one of the two axioms
defining exponentiation in this game.
"

NewLemma MyNat.pow_zero

LemmaDoc MyNat.zero_pow_zero as "zero_pow_zero" in "^" "
Mathematicians sometimes argue that `0 ^ 0 = 0` is also
a good convention. But it is not a good convention in this
game; all the later levels come out beautifully with the
convention that `0 ^ 0 = 1`.
"

/-- $0 ^ 0 = 1$ -/
Statement zero_pow_zero
    : (0 : ℕ) ^ 0  = 1 := by
  rw [pow_zero]
  rfl

LemmaTab "^"
