import Game.Levels.Algorithm.L03add_algo2
import ImportGraph

World "Algorithm"
Level 4
Title "the simplest approach"

TheoremTab "+"

namespace MyNat

macro "simp_add" : tactic => `(tactic|(
  simp only [add_assoc, add_left_comm, add_comm]))

/--
# Overview

Our home-made tactic `simp_add` will solve arbitrary goals of
the form `a + (b + c) + (d + e) = e + (d + (c + b)) + a`.
-/
TacticDoc simp_add

NewTactic simp_add

Introduction
"
You can make your own tactics in Lean.
This code here
```
macro \"simp_add\" : tactic => `(tactic|(
  simp only [add_assoc, add_left_comm, add_comm]))
```
was used to create a new tactic `simp_add`, which runs
`simp only [add_assoc, add_left_comm, add_comm]`.
Try running `simp_add` to solve this level!
"



/-- If $a, b,\ldots h$ are arbitrary natural numbers, we have
$(d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h$. -/
Statement (a b c d e f g h : ℕ) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add

Conclusion
"
Let's now move on to a more efficient approach to questions
involving numerals, such as `20 + 20 = 40`.
"
