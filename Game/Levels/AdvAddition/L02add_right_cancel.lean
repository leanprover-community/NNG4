import Game.Levels.AdvAddition.L01ne_succ_self

World "AdvAddition"
Level 2
Title "add_right_cancel"

namespace MyNat

LemmaTab "Add"

LemmaDoc MyNat.add_right_cancel as "add_right_cancel" in "Add" "

`add_right_cancel a b n` is the theorem that $a+n=b+n \\implies a=b.$
"

Introduction
"`add_right_cancel a b n` is the theorem that $a+n=b+n\\implies a=b$.
"

/-- $a+n=b+n\implies a=b$. -/
Statement add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  Hint (hidden := true) "Start with induction on `n`."
  induction n with d hd
  intro h
  repeat rw [add_zero] at h
  exact h
  intro h
  repeat rw [add_succ] at h
  apply succ_inj at h
  apply hd at h
  exact h

Conclusion "Nice!"
