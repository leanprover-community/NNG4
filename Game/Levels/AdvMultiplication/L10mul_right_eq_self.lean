import Game.Levels.AdvMultiplication.L09mul_left_cancel

World "AdvMultiplication"
Level 10
Title "mul_right_eq_self"

TheoremTab "*"

namespace MyNat

LemmaDoc MyNat.mul_right_eq_self as "mul_right_eq_self" in "*" "
`mul_right_eq_self a b` is a proof that if `a ≠ 0` and `a * b = a` then `b = 1`.
"

Introduction
"The lemma proved in the final level of this world will be helpful
in Divisibility World.
"

Statement mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  Hint (hidden := true) "Reduce to the previous lemma with `nth_rewrite 2 [← mul_one a] at h`"
  nth_rewrite 2 [← mul_one a] at h
  Hint (hidden := true) "You can now `apply mul_left_cancel at h`"
  exact mul_left_cancel a b 1 ha h

Conclusion "
A two-line proof is

```
nth_rewrite 2 [← mul_one a] at h
exact mul_left_cancel a b 1 ha h
```

We now have all the tools necessary to set up the basic theory of divisibility of naturals.
"
