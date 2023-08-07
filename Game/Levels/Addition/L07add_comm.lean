import Game.Levels.Addition.L06succ_add


World "Addition"
Level 7
Title "`add_comm` (sub-boss)"

namespace MyNat

Introduction
"
[boss battle music]

Look in your inventory to see the proofs you have available.
These should be enough.
"

LemmaDoc MyNat.add_comm as "add_comm" in "Add"
"`add_comm x y` is a proof of `x + y = y + x`."

/-- On the set of natural numbers, addition is commutative.
In other words, if `a` and `b` are arbitrary natural numbers, then
$a + b = b + a$. -/
Statement add_comm (a b : ℕ) : a + b = b + a := by
  Hint (hidden := true) "Induction on `a` or `b` -- it's all the same in this one."
  Branch
    induction a with d hd
    · simp
    · simp [succ_add, add_succ, hd]
  induction b with d hd
  · simp
  · simp_all [succ_add, add_succ]

-- Adding this instance to make `ac_rfl` work.
instance : Lean.IsCommutative (α := ℕ) (·+·) := ⟨add_comm⟩

LemmaTab "Add"

Conclusion
"
If you got this far -- nice! There is one more lemma which you will need
from this world, which is the next one: `(a + b) + c = a + (b + c)`, otherwise
known as associativity of addition (note that this is not obvious, for
example subtraction isn't associative). After that you will have to make
a choice.
"
