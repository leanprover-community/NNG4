import Game.Levels.Addition
import Game.MyNat.AdvAddition

World "AdvAddition"
Level 8
Title "add_right_cancel"

namespace MyNat

LemmaTab "Add"

LemmaDoc MyNat.add_right_cancel as "add_right_cancel" in "Add" "

`add_right_cancel a b n` is the theorem that $a+n=b+n \\implies a=b.$
"

NewLemma MyNat.add_right_cancel

Introduction
"`add_right_cancel a b n` is the theorem that $a+n=b+n\\implies a=b$.
Start with `induction n with d hd` and see if you can take it from there.
"

/-- $a+n=b+n\\implies a=b$. -/
Statement add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  induction n with d hd
  intro h
  repeat rw [add_zero] at h
  assumption
  intro h
  repeat rw [add_succ] at h
  apply succ_inj at h
  apply hd at h
  assumption

Conclusion "Nice!"
