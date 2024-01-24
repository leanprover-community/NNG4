import Game.Levels.Addition

World "Algorithm"
Level 1
Title "add_left_comm"

TheoremTab "+"

namespace MyNat

LemmaDoc MyNat.add_left_comm as "add_left_comm" in "+" "
`add_left_comm a b c` is a proof that `a + (b + c) = b + (a + c)`.
"

Introduction "Having to rearrange variables manually using commutativity and
associativity is very tedious. We start by reminding you of this. `add_left_comm`
is a key component in the first algorithm which we'll explain, but we need
to prove it manually.

Remember that you can do precision commutativity rewriting
with things like `rw [add_comm b c]`. And remember that
`a + b + c` means `(a + b) + c`.
"

/-- If $a, b, c$ are numbers, then $a+(b+c)=b+(a+c)$. -/
Statement add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc]
  rw [add_comm a b]
  rw [add_assoc]
  rfl
