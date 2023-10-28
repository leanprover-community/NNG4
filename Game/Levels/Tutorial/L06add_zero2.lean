import Game.Metadata
import Game.MyNat.Addition


World "Tutorial"
Level 6
Title "Precision rewriting"

Introduction
"
## Precision rewriting

In the last level, there was `b + 0` and `c + 0`,
and `rw [add_zero]` changed the first one it saw,
which was `b + 0`. Let's learn how to tell Lean
to change `c + 0` first by giving `add_zero` an
explicit input.
"

namespace MyNat

/-- $a+(b+0)+(c+0)=a+b+c.$ -/
Statement (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  Hint "Try `rw [add_zero c]`."
  rw [add_zero c]
  Hint "`add_zero c` is a proof of `c + 0 = c` so that was what got rewritten.
  You can now change `b + 0` to `b` with `rw [add_zero]` or `rw [add_zero b]`. You
  can usually stick to `rw [add_zero]` unless you need real precision."
  rw [add_zero]
  rfl

LemmaTab "+"

Conclusion "
Let's now learn about Peano's second axiom for addition, `add_succ`.
"
