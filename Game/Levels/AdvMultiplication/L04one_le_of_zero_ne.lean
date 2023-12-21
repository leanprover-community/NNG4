import Game.Levels.AdvMultiplication.L03eq_succ_of_ne_zero

World "AdvMultiplication"
Level 4
Title "one_le_of_ne_zero"

LemmaTab "≤"

namespace MyNat

LemmaDoc MyNat.one_le_of_ne_zero as "one_le_of_ne_zero" in "≤" "
`one_le_of_ne_zero a` is a proof that `a ≠ 0 → 1 ≤ a`.
"

Introduction
"The previous lemma can be used to prove this one.
"

Statement one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  Hint (hidden := true) "Use the previous lemma with `apply eq_succ_of_ne_zero at ha`."
  apply eq_succ_of_ne_zero at ha
  Hint (hidden := true) "Now take apart the existence statement with `cases ha with n hn`."
  cases ha with n hn
  use n
  rw [hn, succ_eq_add_one, add_comm]
  rfl
