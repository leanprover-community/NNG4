import Game.Levels.AdvMultiplication.L08mul_eq_zero

World "AdvMultiplication"
Level 9
Title "mul_left_cancel"

TheoremTab "*"

namespace MyNat

LemmaDoc MyNat.mul_left_cancel as "mul_left_cancel" in "*" "
`mul_left_cancel a b c` is a proof that if `a ≠ 0` and `a * b = a * c` then `b = c`.
"

Introduction
"
In this level we prove that if `a * b = a * c` and `a ≠ 0` then `b = c`. It is tricky, for
several reasons. One of these is that
we need to introduce a new idea: we will need to understand the concept of
mathematical induction a little better.

Starting with `induction b with d hd` is too naive, because in the inductive step
the hypothesis is `a * d = a * c → d = c` but what we know is `a * succ d = a * c`,
so the induction hypothesis does not apply!

Assume `a ≠ 0` is fixed. The actual statement we want to prove by induction on `b` is
\"for all `c`, if `a * b = a * c` then `b = c`. This *can* be proved by induction,
because we now have the flexibility to change `c`.\"
"

Statement mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  Hint "The way to start this proof is `induction b with d hd generalizing c`."
  induction b with d hd generalizing c
  · Hint (hidden := true) "Use `mul_eq_zero` and remember that `tauto` will solve a goal
  if there are hypotheses `a = 0` and `a ≠ 0`."
    rw [mul_zero] at h
    symm at h
    apply mul_eq_zero at h
    cases h with h1 h2
    · tauto
    · rw [h2]
      rfl
  · Hint "The inductive hypothesis `hd` is \"For all natural numbers `c`, `a * d = a * c → d = c`\".
    You can `apply` it `at` any hypothesis of the form `a * d = a * ?`. "
    Hint (hidden := true) "Split into cases `c = 0` and `c = succ e` with `cases c with e`."
    cases c with e
    · rw [mul_succ, mul_zero] at h
      apply add_left_eq_zero at h
      tauto
    · rw [mul_succ, mul_succ] at h
      apply add_right_cancel at h
      apply hd at h
      rw [h]
      rfl
