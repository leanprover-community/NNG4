import Game.Levels.AdvMultiplication.L02mul_left_ne_zero

World "AdvMultiplication"
Level 3
Title "one_le_of_zero_ne"

LemmaTab "≤"

namespace MyNat

LemmaDoc MyNat.one_le_of_zero_ne as "one_le_of_zero_ne" in "≤" "
`one_le_of_zero_ne a` is a proof that `a ≠ 0 → 1 ≤ a`.
"

Introduction
"We need to understand how to use a hypothesis like `a ≠ 0`.
Here is a useful lemma. I talk through how to get started in the hidden hints.
Access them by clicking on \"Show more help!\"
"

Statement one_le_of_zero_ne (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  Hint (hidden := true) "Start with `cases a with n` to do a case split on `a = 0` and `a = succ n`."
  cases a with n
  · Hint (hidden := true) "You have a false hypothesis so you can just solve this with the logic
  tactic `tauto`."
    tauto
  · use n
    rw [succ_eq_add_one]
    rw [add_comm]
    rfl
