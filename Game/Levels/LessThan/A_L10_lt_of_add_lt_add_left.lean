import Game.Levels.LessThan.A_L09_lt_succ_iff_le

World "LessThan"
Level 10
Title "We can cancel an addend from both sides of an inequality"

TheoremTab "<"

namespace MyNat

/-- `lt_of_add_lt_add_left a b c` is a proof that `a + b < a + c → b < c`.-/
TheoremDoc MyNat.lt_of_add_lt_add_left as "lt_of_add_lt_add_left" in "<"

Introduction "In this level we show that we can always cancel an
addend from both sides of an inequality.  Our overall goal is to produce
a number morally equal to `c - succ b`."


/--
We can cancel an addend from both sides of an inequality and retain
an inequality.
-/
Statement lt_of_add_lt_add_left (a b c : ℕ) : a + b < a + c → b < c := by
  intro h0
  Hint "Our goal is to use `add_left_cancel`, so `cases
  {h0} with n hn` will make progress"
  cases h0 with n hn
  Hint "What number is `c - succ b`?"
  rw [succ_add,add_assoc,←add_succ,←add_succ] at hn
  have h1 := add_left_cancel c (b + succ n) a hn
  use n
  rw [h1,add_succ,succ_add]
  rfl

Conclusion "
My Proof:
```
  intro h0
  cases h0 with n hn
  rw [succ_add,add_assoc,←add_succ,←add_succ] at hn
  have h1 := add_left_cancel c (b + succ n) a hn
  use n
  rw [h1,add_succ,succ_add]
  rfl
```
"
