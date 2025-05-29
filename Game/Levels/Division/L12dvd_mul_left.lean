import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms

World "Division"
Level 12
Title ""

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if a | b  then a | c*b for all a,b,c ∈ ℕ.
"
/-- `dvd_mul_left a b c` is a proof that if `a | b` then `a | c*b` .-/
TheoremDoc MyNat.dvd_mul_left as "dvd_mul_left" in "∣"

Statement dvd_mul_left
    (a b c : ℕ) (h1 : a ∣ b) : a ∣ c*b := by
  cases h1 with k1 h11
  use k1*c
  rw [<- mul_assoc]
  rw [h11]
  rw [mul_comm]
  rfl

/-- import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms

World "Division"
Level 12
Title ""

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if a | b  and a ≠ b then ¬ (b ∣ a) for all a,b ∈ ℕ.
"
/-- `dvd_not_eq a b c` is a proof that if `a | b` and `a ≠ b` then `¬ (b ∣ a)` .-/
TheoremDoc MyNat.dvd_not_eq as "dvd_not_eq" in "∣"

Statement dvd_not_eq
  (a b : ℕ) (h1 : a ∣ b) (h2 : a ≠ b) : ¬ (b ∣ a) := by
 intro h
  cases h1 with k hk       -- b = a * k
  cases h with m hm        -- a = b * m
  rw [hk] at hm            -- a = (a * k) * m
  rw [mul_assoc] at hm     -- a = a * (k * m)
  symm at hm               -- a * (k * m) = a
  have ha : a ≠ 0 := by
    intro h0
    rw [h0,zero_mul] at hk
    rw [hk] at h2
    contradiction        -- contradiction: a = b
  have hkm := mul_right_eq_self a (k*m) ha
  apply hkm at hm
  apply mul_right_eq_one at hm
  rw[hm,mul_one] at hk
  tauto
--/
