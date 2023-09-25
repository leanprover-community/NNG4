import Game.Levels.Multiplication.L03succ_mul


World "Multiplication"
Level 4
Title "mul_comm"

namespace MyNat

Introduction
"
When you've proved this theorem you will have \"spare\" proofs
such as `zero_mul`, which is now easily deducible from `mul_zero`.
But we keep hold of these theorems anyway, because often it's convenient
to have exactly the right tool for a job.
"

LemmaDoc MyNat.mul_comm as "mul_comm" in "Mul" "
`mul_comm` is the proof that multiplication is commutative. More precisely,
`mul_comm a b` is the proof that `a * b = b * a`.
"

/-- Multiplication is commutative. -/
Statement mul_comm
    (a b : ℕ) : a * b = b * a := by
  induction b with d hd
  · rw [zero_mul]
    rw [mul_zero]
    rfl
  · rw [succ_mul]
    rw [← hd]
    rw [mul_succ]
    rfl

LemmaTab "Mul"
