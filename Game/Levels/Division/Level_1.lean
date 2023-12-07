import Game.Levels.Multiplication
import Game.MyNat.Division

World "Division"
Level 1
Title "one_dvd"

LemmaTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that 1 ∣ n for all n ∈ ℕ. `a | b` is
  shorthand for `there exists a number c such that `b = c * a`, because of
  `exists`, the use statment will be useful here.

"

LemmaDoc MyNat.one_dvd as "one_dvd" in "∣" "
`one_div x` is a proof that `1 ∣ x`.
"

Statement one_dvd
    (n : ℕ) :  1 ∣ n := by
  Hint "The reason `1 ∣ n` is because `n = n * 1`, so you should
  start this proof with `use n`."
  use n
  rw [one_mul]
  rfl


Conclusion
"
  Congratulations! You have proven your first theorem about division.
"
