import Game.Metadata
import Game.MyNat.Addition

World "Addition"
Level 5
Title "That's it."

--namespace MyNat
namespace MyNat

Introduction
"
  Let `x` be a fixed natural number and let us consider the problem of working out
  `x + y` for some other natural number `y`. Now Peano did not give us a formula for
  `x + y`; he did however give us formulas for `x + 0` and for `x + succ d`.
  The point of Peano's third axiom \"That's it\" is that *every* natural number
  can be built from `0` and `succ`, so we can conclude that Peano's formulas
  for addition do cover every case for `y`. This means that `x + y` is well-defined
  for all `x` and `y`. Formally, this is a *proof by induction*; indeed another
  way of explaining \"That's it!\" is to say that constructions by recursion and
  proofs by induction are valid for natural numbers. For those of you who haven't
  seen it, induction is the proof strategy which regards the natural numbers
  like a line of dominos: the base case is that you knock the 0th domino over,
  and the inductive step is the observation that if the `n`th domino falls down
  then so does the `succ n`'th domino. The conclusion is that an arbitrary domino
  will fall down sooner or later.


OK so let's see induction in action. We're going to prove

```
zero_add (n : ℕ) : 0 + n = n
```

Wait… what is going on here? Isn't this one of the axioms? Unfortunately not:
the axiom was `add_zero n : n + 0 = n`, which is slightly different. But isn't
`n + 0` obviously equal to `0 + n`? Indeed isn't `x + y` equal to `y + x`?
This is true, but this is the next sub-boss! This result is called commutativity
of addition, and it will be proved in level 7. In particular, *we cannot use it yet*.

The difficulty with proving `0 + n = n` is that we do not have a *formula* for
`0 + n`, we can only do `0 + n` if we know whether `n` is zero or a successor.
The `induction` tactic splits into these cases.  The base case will require
us to prove `0 + 0 = 0` and the inductive step will ask us to show that
if `0 + d = d` then `0 + succ d = succ d`. These questions are more tractable
because we have formulas for adding `0` and adding successors. See if you
can do your first induction proof in Lean.
"

LemmaDoc MyNat.zero_add as "zero_add" in "Add" "`zero_add x` is the proof that `0 + x = x`. It's
a `simp` lemma, because replacing `0 + x` by `x` is almost always what you want
to do if you're simplifying. "

/-- For all natural numbers $n$, we have $0 + n = n$. -/
Statement zero_add (n : ℕ) : 0 + n = n := by
  Hint "You can start a proof by induction over `n` by typing:
  `induction n with d hd`."
  induction n with d hd
  · Hint "Now you have two goals. Once you proved the first, you will jump to the second one.
    This first goal is the base case $n = 0$.

    Recall that you can use all lemmas that are visible in your inventory."
    Hint (hidden := true) "try using `add_zero`."
    rw [add_zero]
    rfl
  · Hint "Now you jumped to the second goal. Here you have the induction hypothesis
    `{hd} : 0 + {d} = {d}` and you need to prove the statement for `succ {d}`."
    Hint (hidden := true) "look at `add_succ`."
    rw [add_succ]
    Hint (hidden := true) "At this point you see the term `0 + {d}`, so you can use the
    induction hypothesis with `rw [{hd}]`."
    rw [hd]
    rfl

attribute [simp] zero_add

TacticDoc induction "
## Summary

if `n : MyNat` is in our assumptions, then `induction n with d hd`
attempts to prove the goal by induction on `n`, with the inductive
variable in the `succ` case being `d`, and the inductive hypothesis being `hd`.

## Details

If you have a natural number `n : MyNat` in your assumptions
then `induction n with d hd` turns your
goal into two goals, a base case with `n = 0` and
an inductive step where `hd` is a proof of the `n = d`
case and your goal is the `n = succ d` case.

### Example:
If this is our local context:
```
n : mynat
⊢ 2 * n = n + n
```

then

`induction n with d hd`

will give us two goals:

```
⊢ 2 * 0 = 0 + 0
```

and
```
d : mynat,
hd : 2 * d = d + d
⊢ 2 * succ d = succ d + succ d
```

-/

"
NewTactic induction
LemmaTab "Add"

Conclusion
"
## Now venture off on your own for a while.

Those three tactics:

* `induction n with d hd`
* `rw [h]`
* `rfl`

will get you quite a long way through this game. Using only these tactics
you can beat the next sub-boss, level 7 of addition world: `add_comm x y : x + y = y + x`.
You can also beat much of Multiplication World including the boss `a * b = b * a`,
and even all of Power World including the fiendish final boss. This route will
give you a good grounding in these three basic tactics; after that, if you
are still interested, there are other worlds to master like advanced addition
world, where you can learn more tactics.

But we're getting ahead of ourselves, you still have to beat the rest of Addition World.
We're going to stop explaining stuff carefully now. If you get stuck or want
to know more about Lean (e.g. how to do much harder maths in Lean),
ask in `#new members` at
[the Lean chat](https://leanprover.zulipchat.com)
(login required, real name preferred). Any of the people there might be able to help.

Good luck! Click on \"Next\" to solve some levels on your own.
"
