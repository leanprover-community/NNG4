import Game.Levels.Addition.L05zero_add


World "Addition"
Level 6
Title "succ_add"

namespace MyNat

Introduction
"
Oh no! On the way to `add_comm`, a wild `succ_add` appears. `succ_add`
is the proof that `succ(a) + b = succ(a + b)` for `a` and `b` in your
natural number type. If we knew `add_comm` already we could use that and
`add_succ`, but we don't. Indeed we will need `add_succ` to defeat
`add_comm : ∀ a b, a + b = b + a` in the next level.

NB: think about why computer scientists called this result `succ_add` .
There is a logic to all the names.

Note that if you want to be more precise about exactly where you want
to rewrite something like `add_succ` (the proof you already have),
you can do things like `rw [add_succ (succ a)]` or
`rw [add_succ (succ a) d]`, telling Lean explicitly what to use for
the input variables for the function `add_succ`. Indeed, `add_succ`
is a function: it takes as input two variables `a` and `b` and outputs a proof
that `a + succ(b) = succ(a + b)`. The tactic `rw [add_succ]` just says to Lean \"guess
what the variables are\".
"

LemmaDoc MyNat.succ_add as "succ_add" in "MyNat" "`succ_add a b` is a proof that `succ a + b = succ (a + b)`."
/-- For all natural numbers $a, b$, we have
$ \\operatorname{succ}(a) + b = \\operatorname{succ}(a + b)$. -/
Statement succ_add
    (a b : ℕ) : succ a + b = succ (a + b)  := by
  Hint (hidden := true) "You might want to think about whether induction
  on `a` or `b` is the best idea."
  Branch
    induction a with d hd
    Hint "Induction on `a` will not work. Addition is defined by recursion
    on the second variable, so you need to do induction on the second
    variable in the additions"
  induction b with d hd
  · Hint (hidden := true) "Instead of two rewrites and a `rfl` can you find a
    tactic which proves `succ a + 0 = succ (a + 0)` immediately?"
    simp
  · Hint (hidden := true) "You can solve this goal in one line with a high-powered tactic"
    Hint (hidden := true) "It's `simp` but you'll need to feed `simp` the right list of
    lemmas to use..."
    simp [add_succ, hd]

LemmaTab "Add"

Conclusion
"

"
