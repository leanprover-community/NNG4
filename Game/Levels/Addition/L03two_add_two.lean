import Game.Metadata
import Game.MyNat.Addition
import Game.MyNat.DecidableEq
World "Addition"
Level 3
Title "Two add two is four."

--namespace MyNat
namespace MyNat

Introduction
"
If you need to know the statements of Peano's axioms or the names of the lemma
about succ 3 and 4, just look at the blah blah I have no idea.
"

Statement MyNat.two_add_two
"$2+2=4$."
    : (2 : ℕ) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  rw [add_succ, one_eq_succ_zero, add_succ, add_zero, four_eq_succ_three, three_eq_succ_two]
  rfl

LemmaTab "Add"

Conclusion
"
  Nice. Maybe in the next level we do 2375 + 6947?
  Are you up for the first sub-boss `2 + 2 = 4`?
"
