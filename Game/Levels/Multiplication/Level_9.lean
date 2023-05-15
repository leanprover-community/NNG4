import Game.Levels.Multiplication.Level_8


World "Multiplication"
Level 9
Title "mul_left_comm"

open MyNat

Introduction
"
You are equipped with

* `mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c)`
* `mul_comm (a b : ℕ) : a * b = b * a`

Re-read the docs for `rw` so you know all the tricks.
You can see them in your inventory on the right.

"

-- TODO
attribute [simp] MyNat.mul_zero
attribute [simp] MyNat.mul_succ
attribute [simp] MyNat.zero_mul
attribute [simp] MyNat.succ_mul
attribute [simp] MyNat.mul_one
attribute [simp] MyNat.one_mul

Statement MyNat.mul_left_comm
"For all natural numbers $a$ $b$ and $c$, we have $a(bc)=b(ac)$."
    (a b c : ℕ) : a * (b * c) = b * (a * c) := by
  Branch
    induction c
    · simp
    · simp
      rw [mul_add, n_ih, mul_add, mul_comm a b]
      rfl
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]
  rfl

LemmaTab "Mul"

-- TODO: make simp work:
-- attribute [simp] mul_assoc mul_comm mul_left_comm

Conclusion
"
Now we add a lot of the lemmas you proved to the `simp`, so it can do simplifications

If you feel like attempting Advanced Multiplication world
you'll have to do Function World and the Proposition Worlds first.
These worlds assume a certain amount of mathematical maturity
(perhaps 1st year undergraduate level).
Your other possibility is Power World, with the \"final boss\".
"

-- -- TODO: Is it not bad habit that `simp` can prove these? If `simp`
-- -- solves algebraic equations it's more by accident than by clever algorithm... that's `ring`.
-- And now I whisper a magic incantation

-- ```
-- attribute [simp] mul_assoc mul_comm mul_left_comm
-- ```

-- and all of a sudden Lean can automatically do levels which are
-- very boring for a human, for example

-- ```
-- example (a b c d e : ℕ) :
--     (((a * b) * c) * d) * e = (c * ((b * e) * a)) * d := by
--   simp
-- ```
