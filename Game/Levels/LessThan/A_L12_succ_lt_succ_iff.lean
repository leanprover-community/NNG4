import Game.Levels.LessThan.A_L11_add_lt_add_right

World "LessThan"
Level 12
Title "succ_lt_succ_iff"

TheoremTab "<"

namespace MyNat

/--
succ_lt_succ_iff a b` is a proof that shows that `succ a < succ b ↔ a < b`.
-/
TheoremDoc MyNat.succ_lt_succ_iff as "succ_lt_succ_iff" in "<"

Introduction "This is the `<`-world partner of `succ_le_succ_iff` from
`≤`-world.  The proof is not complicated.  A short proof is possible
by using `lt_succ_iff_le`, and the definition of `<`."



Statement succ_lt_succ_iff (a b : ℕ) : a < b ↔ succ a < succ b := by
  rw [lt_succ_iff_le (succ a) b]
  Hint"Question for Kevin, Why can't I just use 'rfl' here?"
  --rfl
  --Question for Kevin.  Why can't I just use `rfl` here?
  --My understanding is that `a<b` is defined to be `succ a ≤ b`.
  --I ended up adding a theorem in Game/MyNat/LT.lean
  --
  --theorem lt_iff_succ_le (a b : ℕ) : a < b ↔ succ a ≤ b := by rfl
  --and it didn't complain
  --Edit to add: acually it is now complaining, so I don't know.
  --
  exact (lt_iff_succ_le a b).symm


Conclusion
"My Proof:
```
repeat rw [lt_iff_succ_le]
exact succ_le_succ_iff (succ a) b
```
"
