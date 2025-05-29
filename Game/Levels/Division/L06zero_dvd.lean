import Game.Levels.Multiplication
import Game.MyNat.Division

World "Division"
Level 6
Title "zero_dvd"

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if 0 ∣ n then n = 0 for all n ∈ ℕ. In other words,
  the only number 0 can divide is itself.
"
/-- `zero_dvd n` is a proof that if `0 ∣ n` then n = 0.-/
TheoremDoc MyNat.zero_dvd as "zero_dvd" in "∣"

Statement zero_dvd
    (n : ℕ) (h :  0∣n) : n = 0 := by
      cases h with k h1
      rw [zero_mul] at h1
      rw [h1]
      rfl

Conclusion
"
  Very well done! .
"
