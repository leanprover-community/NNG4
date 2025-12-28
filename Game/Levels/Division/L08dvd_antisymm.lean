
import Game.Levels.AdvMultiplication
import Game.MyNat.Division

World "Division"
Level 8
Title "dvd_antisymm"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that `divides` is antisymmetric. i.e the
  only way that we can have `a | b` and `b | a` is if `a = b`.
"

/-- div_antisymm a b` is a proof that `if a ∣ b and b ∣ a, then a = b`.-/
TheoremDoc MyNat.dvd_antisymm as "dvd_antisymm" in "∣"

Statement dvd_antisymm
    (a b : ℕ) (h1 : a ∣ b) (h2 : b ∣ a): a = b := by
  cases h1 with m hm       
  cases h2 with n hn       
  rw [hn] at hm             
  Hint (hidden := true) "Try casing on b"
  cases b with b'
  rw [zero_mul] at hn     
  rw [hn]
  rfl
  rw [mul_assoc] at hm    
  symm at hm              
  Hint (hidden := true) "Think of what hypothesis can be introduced here that could help solve this step."
  have ha : succ b' ≠ 0 := succ_ne_zero b'
  apply mul_right_eq_self at hm   
  apply mul_right_eq_one at hm          
  rw [hm, mul_one] at hn
  exact hn
  exact ha

Conclusion
"
  Well done, if you solved this level then you should be fine with the next level!
"
