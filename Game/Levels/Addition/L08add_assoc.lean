import Game.Levels.Addition.L07add_comm


World "Addition"
Level 8
Title "add_assoc (associativity of addition)"

namespace MyNat

Introduction
"
It's well-known that $(1 + 2) + 3 = 1 + (2 + 3)$; if we have three numbers
to add up, it doesn't matter which of the additions we do first. This fact
is called *associativity of addition* by mathematicians, and it is *not*
obvious. For example, subtraction really is not associative: $(6 - 2) - 1$
is really not equal to $6 - (2 - 1)$. We are going to have to prove
that addition, as defined the way we've defined it, is associative.

See if you can prove associativity of addition. Note that now we have
`zero_add` as well as `add_zero`, and `succ_add` as well as `add_succ`,
it probably doesn't matter which variable we induct on. Take your pick!
"

LemmaDoc MyNat.add_assoc as "add_assoc" in "MyNat" "`add_assoc a b c` is a proof
that `(a + b) + c = a + (b + c)`. Note that in Lean `(a + b) + c` prints
as `a + b + c`, because the notation for addition is defined to be left
associative. "

Statement add_assoc
"On the set of natural numbers, addition is associative.
In other words, if $a, b$ and $c$ are arbitrary natural numbers, we have
$ (a + b) + c = a + (b + c). $"
    (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  Hint "Note that when Lean writes `a + b + c`, it means `(a + b) + c`. If it wants to talk
  about `a + (b + c)` it will put the brackets in explictly."
  Branch
    induction a with d hd
    simp
    simp [succ_add, hd]
  Branch
    induction b with d hd
    simp
    simp [succ_add, add_succ, hd]
  induction c with c hc
  simp
  simp [hc, succ_add, add_succ]

NewLemma MyNat.add_assoc
LemmaTab "Add"

Conclusion
"
Congratulations, you just proved that the naturals are an additive commutative monoid!

You have also proved all the lemmas you need to be able to start on multiplication
world. However there are still three more levels left in addition world, with
the final boss being `(d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h`,
a level which we will solve in one line.
"
