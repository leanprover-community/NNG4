import Game.Levels.AdvMultiplication

World "Division"
Level 7
Title "ndiv_succ"

namespace MyNat

Introduction
"
  In this section we will prove a similar reslult to div_add_right, but for multiplication.
"

LemmaDoc MyNat.ndiv_succ as "ndiv_succt" in "∣" "
`ndiv_succ a b` is a proof that `if a ≠ 1 and a ∣ b, then ¬ a ∣ succ b`.
"

NewLemma MyNat.ndiv_succ

Statement
    (a b : ℕ) (ha : a ≠ 1) (hab : a ∣ b) : ¬ a ∣ succ b := by
    sorry


LemmaTab "∣"
