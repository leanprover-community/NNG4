import Game.Levels.AdvMultiplication.L04le_mul_right

World "AdvMultiplication"
Level 5
Title "le_one"

LemmaTab "≤"

namespace MyNat

LemmaDoc MyNat.le_one as "le_one" in "≤" "
`le_one a b` is a proof that `a * b ≠ 0 → a ≤ a * b`.

It's one way of saying that a divisor of a positive number
has to be at most that number.
"

Introduction
"We could have proved this result in ≤ World. I leave some hidden hints.
"

Statement le_one (a : ℕ) (ha : a ≤ 1) : a = 0 ∨ a = 1 := by
  Hint (hidden := true) "Start with `cases a with b` to break into `a = 0` and `a = succ b` cases."
  cases a with b
  · left
    rfl
  · Hint (hidden := true) "Now `cases b with c`."
    cases b with c
    · right
      rw [one_eq_succ_zero]
      rfl
    · Hint (hidden := true) "Now `cases ha with x hx` and work on `hx` until it's `False`.
      Then use a logic tactic to finish."
      cases ha with x hx
      rw [succ_add, succ_add] at hx
      rw [one_eq_succ_zero] at hx
      apply succ_inj at hx
      apply zero_ne_succ at hx
      Hint (hidden := true) "Now finish with `tauto`."
      tauto
