import Game.Levels.AdvMultiplication


World "Division"
Level 1
Title "one_div"

namespace MyNat

Introduction
"
  In this section, we will prove that 1 ∣ n for all n ∈ ℕ. `a | b` is
  shorthand for `there existsw a number c such that `b = c * a``, so
  you should be looking to use the `use' tactic in these kinds of proof.

"

LemmaDoc MyNat.one_div as "one_div" in "∣" "
`one_div x` is a proof that `1 ∣ x`.
"

NewLemma MyNat.one_div

Statement
    (n : ℕ) : 1 ∣ n := by
  Hint "The reason `1 ∣ n` is because `n = n * 1`, so you should
  start this proof with `use n`."
  use n

LemmaTab "∣"
