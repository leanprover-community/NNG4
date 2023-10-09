import Game.Levels.AdvAddition.Level_11



World "AdvAddition"
Level 12
Title "add_one_eq_succ"

open MyNat

Introduction
"
We have

```
succ_eq_add_one (n : ℕ) : succ n = n + 1
```

but sometimes the other way is also convenient.
"

/-- For any natural number $d$, we have
$$ d+1 = \operatorname{succ}(d). $$ -/
Statement MyNat.add_one_eq_succ
    (d : ℕ) : d + 1 = succ d := by
  rw [succ_eq_add_one]
  rfl

LemmaTab "Add"

Conclusion
"

"
