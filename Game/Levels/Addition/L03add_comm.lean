import Game.Levels.Addition.L02succ_add


World "Addition"
Level 3
Title "add_comm (level boss)"

namespace MyNat

Introduction
"
[boss battle music]

Look in your inventory to see the proofs you have available.
These should be enough.
"

LemmaDoc MyNat.add_comm as "add_comm" in "+"
"`add_comm x y` is a proof of `x + y = y + x`."

/-- On the set of natural numbers, addition is commutative.
In other words, if `a` and `b` are arbitrary natural numbers, then
$a + b = b + a$. -/
Statement add_comm (a b : ℕ) : a + b = b + a := by
  Hint (hidden := true) "Induction on `a` or `b` -- it's all the same in this one."
  induction b with d hd
  · rw [add_zero, zero_add]
    rfl
  · rw [add_succ, succ_add, hd]
    rfl

-- Adding this instance to make `ac_rfl` work.
instance : Lean.IsCommutative (α := ℕ) (· + ·) := ⟨add_comm⟩

TheoremTab "+"
