import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial
-- note that
-- import Game.Levels.Tutorial.L05add_succ
-- breaks the game server -- text disappears from
-- tutorial world intro level!

World "Addition"
Level 1
Title "zero_add"

namespace MyNat

Introduction
"
In this level we're going to prove that $0+n=n$, where $n$ is a secret natural number.

Wait, don't we already know that? No! We know that $n+0=n$, but that's `add_zero`.
This is `zero_add`, which is different.

The difficulty with proving `0 + n = n` is that we do not have a *formula* for
`0 + n` in general, we can only use `add_zero` and `add_succ` once
we know whether `n` is `0` or a successor. The `induction` tactic splits into these two cases.

The base case will require us to prove `0 + 0 = 0`, and the inductive step
will ask us to show that if `0 + d = d` then `0 + succ d = succ d`. Because
`0` and successor are the only way to make numbers, this will cover all the cases.

See if you can do your first induction proof in Lean.
"

LemmaDoc MyNat.zero_add as "zero_add" in "+" "
`zero_add x` is the proof of `0 + x = x`.

`zero_add` is a `simp` lemma, because replacing `0 + x` by `x`
is almost always what you want to do if you're simplifying an expression."

/-- For all natural numbers $n$, we have $0 + n = n$. -/
Statement zero_add (n : ℕ) : 0 + n = n := by
  Hint "You can start a proof by induction on `n` by typing:
  `induction n with d hd`."
  induction n with d hd
  · Hint "Now you have two goals. Once you proved the first, you will jump to the second one.
    This first goal is the base case $n = 0$.

    Recall that you can rewrite the proof of any lemma which is visible
    in your inventory, or of any assumption displayed above the goal,
    as long as it is of the form `X = Y`."
    Hint (hidden := true) "try rewriting `add_zero`."
    rw [add_zero]
    rfl
  · Hint "Now for to the second goal. Here you have the induction hypothesis
    `{hd} : 0 + {d} = {d}`, and you need to prove that `0 + succ {d} = succ {d}`."
    Hint (hidden := true) "Use `add_succ`."
    rw [add_succ]
    Hint (hidden := true) "At this point you see the term `0 + {d}`, so you can use the
    induction hypothesis with `rw [{hd}]`."
    rw [hd]
    rfl

attribute [simp] zero_add

TacticDoc induction "
## Summary

If `n : ℕ` is an object, and the goal mentions `n`, then `induction n with d hd`
attempts to prove the goal by induction on `n`, with the inductive
variable in the successor case being `d`, and the inductive hypothesis being `hd`.

### Example:
If the goal is
```
0 + n = n
```

then

`induction n with d hd`

will turn it into two goals. The first is `0 + 0 = 0`;
the second has an assumption `hd : 0 + d = d` and goal
`0 + succ d = succ d`.

Note that you must prove the first
goal before you can access the second one.
"
NewTactic induction

TheoremTab "+"

Conclusion
"
  This lemma would have been easy if we had known that `x + y = y + x`. That theorem
  is called `add_comm` and it is *true*, but unfortunately its proof *uses* both
  `add_zero` and `zero_add`!

  Let's continue on our journey to `add_comm`, the proof of `x + y = y + x`.
"
