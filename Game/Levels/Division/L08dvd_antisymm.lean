
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
  only way that we can have `a | b` and `b | a ` is if a = b.
"

/-- div_antisymm a b` is a proof that `if a ∣ b and b ∣ a, then a = b`.-/
TheoremDoc MyNat.dvd_antisymm as "dvd_antisymm" in "∣"

Statement dvd_antisymm
    (a b : ℕ) (h1 : a ∣ b) (h2 : b ∣ a): a = b := by
  cases h1 with m hm        -- b = a * m
  cases h2 with n hn        -- a = b * n
  rw [hn] at hm             -- a = (a * m) * n
  cases b with b'
  rw [zero_mul] at hn     -- a = 0
  rw [hn]
  rfl
  rw [mul_assoc] at hm    -- a = a * (m * n)
  symm at hm              -- a * (m * n) = a
  have ha : succ b' ≠ 0 := succ_ne_zero b'
  apply mul_right_eq_self at hm    -- concludes m * n = 1
  apply mul_right_eq_one at hm           -- from m * n = 1 → m = 1 ∧ n = 1
  rw [hm, mul_one] at hn
  exact hn
  exact ha
