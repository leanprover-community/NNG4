import Game.Levels.Algorithm.L05is_zero

World "Algorithm"
Level 6
Title "An algorithm for equality"

LemmaTab "Peano"

namespace MyNat

Introduction
"
Every natural is either `0` or `succ n` for some `n`. Here is an algorithm
which, given two naturals `a` and `b`, returns the answer to \"does `a = b`?\"

*) If they're both `0`, return \"yes\".

*) If one is `0` and the other is `succ n`, return \"no\".

*) If `a = succ m` and `b = succ n`, then return the answer to \"does `m = n`?\"

Let's prove that this algorithm always gives the correct answer. The proof that
`0 = 0` is `rfl`. The proof that `0 ≠ succ n` is `zero_ne_succ n`, and the proof
that `succ m ≠ 0` is `succ_ne_zero m`. The proof that if `h : m = n` then
`succ m = succ n` is `rw [h]` and then `rfl`. The next level is a proof of the one
remaining case: if `a ≠ b` then `succ a ≠ succ b`.
"

TacticDoc «have» "
# Summary

The `have` tactic can be used to add new hypotheses to a level, but of course
you have to prove them.

## Example

If you already have naturals `a` and `b` in your context, then

`have h2 : succ a = succ b → a = b := succ_inj a b`

will explicitly add a new hypothesis `h2 : succ a = succ b → a = b`
to the context, because you just supplied the proof of it (`succ_inj a b`).

## Example

If you don't state which statement you are proving, then Lean can
usually work it out anyway. For example

`have h2 := succ_inj a b`

will add the hypothesis `h2 : succ a = succ b → a = b` to your context.

## Example

If you don't supply a proof of the hypothesis you are claiming, then
Lean will simply create another goal for you to prove. For example
if you have `a` in your context and you execute

`have h : a = 0`

then you will get a new goal `a = 0` to prove, and after you've proved
it you will have a new hypothesis `h : a = 0` in your original goal.
"

NewTactic «have»

LemmaDoc MyNat.succ_ne_succ as "succ_ne_succ" in "Peano" "
`succ_ne_succ m n` is the proof that `m ≠ n → succ m ≠ succ n`.
"

/-- If $a \neq b$ then $\operatorname{succ}(a) \neq\operatorname{succ}(b)$. -/
Statement succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  Hint "Start by adding `succ a = succ b → a = b` to our list of hypotheses,
  with `have h2 := succ_inj m n`."
  have := succ_inj m n
  Hint "Now the goal can be solved by pure logic, so use a logic tactic."
  Hint (hidden := true) "Use `tauto`."
  tauto
