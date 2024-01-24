import Game.Levels.Multiplication.L07mul_add

World "Multiplication"
Level 8
Title "add_mul"

namespace MyNat

Introduction
"
`add_mul` is just as fiddly to prove by induction; but there's a trick
which avoids it. Can you spot it?
"

TheoremDoc MyNat.add_mul as "add_mul" in "*" "
`add_mul a b c` is a proof that $(a+b)c=ac+bc$.
"
/-- Addition is distributive over multiplication.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$(a + b) \times c = ac + bc$. -/
Statement add_mul
    (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add]
  repeat rw [mul_comm c]
  rfl

TheoremTab "*"

Conclusion "
Here's my proof:
```
rw [mul_comm, mul_add]
repeat rw [mul_comm c]
rfl
```
"
