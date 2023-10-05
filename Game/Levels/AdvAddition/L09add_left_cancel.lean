import Game.Levels.AdvAddition.L08add_right_cancel

World "AdvAddition"
Level 9
Title "add_left_cancel"

namespace MyNat

LemmaTab "Add"

LemmaDoc MyNat.add_left_cancel as "add_left_cancel" in "Add" "

`add_left_cancel a b n` is the theorem that $n+a=n+b \\implies a=b.$
"

NewLemma MyNat.add_left_cancel

Introduction
"`add_left_cancel a b n` is the theorem that $n+a=n+b\\implies a=b$.
You can prove it by induction on `n` or you can deduce it from `add_left_cancel`.
"

/-- $a+n=b+n\implies a=b$. -/
Statement add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  repeat rw [add_comm n]
  intro h
  apply add_right_cancel at h
  assumption
