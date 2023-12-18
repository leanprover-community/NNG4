import Game.Levels.Implication.L08ne

World "Implication"
Level 9
Title "zero_ne_succ"

LemmaTab "012"

namespace MyNat

LemmaDoc MyNat.zero_ne_succ as "zero_ne_succ" in "Peano" "

`zero_ne_succ n` is the proof that `0 ≠ succ n`.

In Lean, `a ≠ b` is *defined to mean* `a = b → False`. Hence
`zero_ne_succ n` is really a proof of `0 = succ n → False`.
Here `False` is a generic false statement. This means that
you can `apply zero_ne_succ at h` if `h` is a proof of `0 = succ n`.
"

NewLemma MyNat.zero_ne_succ

Introduction "
As warm-up for `2 + 2 ≠ 5` let's prove `0 ≠ 1`. To do this we need to
introduce Peano's last axiom `zero_ne_succ n`, a proof that `0 ≠ succ n`.
To learn about this result, click on it in the list of lemmas on the right.
"

LemmaDoc MyNat.zero_ne_one as "zero_ne_one" in "012" "
`zero_ne_one` is a proof of `0 ≠ 1`.
"

/-- $0\neq1$. -/
Statement zero_ne_one : (0 : ℕ) ≠ 1 := by
  Hint "Start with `intro h`."
  intro h
  Hint "Now change `1` to `succ 0` in `h`."
  rw [one_eq_succ_zero] at h  -- **TODO** this line is not needed :-/
  Hint "Now you can `apply zero_ne_succ at h`."
  apply zero_ne_succ at h -- **TODO** cripple `apply`.
  exact h

Conclusion "Nice!"
