import Game.Levels.Addition.L03add_comm


World "Addition"
Level 4
Title "add_assoc (associativity of addition)"

namespace MyNat

Introduction
"
  We've been adding up two numbers; in this level we will add up three.

  What does $x+y+z$ *mean*? It could either mean $(x+y)+z$, or it
  could mean $x+(y+z)$. In Lean, $x+y+z$ means $(x+y)+z$.

  But why do we care which one it means; $(x+y)+z$ and $x+(y+z)$ are *equal*!

  That's true, but we didn't prove it yet. Let's prove it now by induction.
"

TheoremDoc MyNat.add_assoc as "add_assoc" in "+" "`add_assoc a b c` is a proof
that `(a + b) + c = a + (b + c)`. Note that in Lean `(a + b) + c` prints
as `a + b + c`, because the notation for addition is defined to be left
associative. "

/-- On the set of natural numbers, addition is associative.
In other words, if $a, b$ and $c$ are arbitrary natural numbers, we have
$ (a + b) + c = a + (b + c). $ -/
Statement add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  Hint "Remember that when Lean writes `a + b + c`, it means `(a + b) + c`.
  If you are not sure where the brackets are in an expression, just hover
  your cursor over it and look at what gets highlighted. For example,
  hover over both `+` symbols on the left hand side of the goal and
  you'll see where the invisible brackets are."
  induction c with d hd
  · rw [add_zero, add_zero]
    rfl
  · rw [add_succ, add_succ, hd, add_succ]
    rfl

-- Adding this instance to make `ac_rfl` work.
instance : Lean.IsAssociative (α := ℕ) (· + ·) := ⟨add_assoc⟩

TheoremTab "+"

Conclusion
"
A passing mathematician congratulates you on proving that naturals
are an additive commutative monoid.

Let's practice using `add_assoc` and `add_comm` in one more level,
before we leave addition world.
"
