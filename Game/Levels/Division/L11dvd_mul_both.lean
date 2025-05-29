import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication
import Game.MyNat.Division
import Game.MyNat.PeanoAxioms

World "Division"
Level 11
Title ""

TheoremTab "∣"

namespace MyNat

Introduction
"
  In this level, we will prove that if a | b  then a*c | b*c for all a,b,c ∈ ℕ.
"
/-- `dvd_mul_both a b c` is a proof that if `a | b` then `a*c | b*c` .-/
TheoremDoc MyNat.dvd_mul_both as "dvd_mul_both" in "∣"

Statement dvd_mul_both
    (a b c  : ℕ) (h1 : a ∣ b) : ( a*c ∣ b*c ) := by
    cases h1 with d hd
    use d
    rw [hd]
    rw [mul_assoc]
    rw [mul_comm d c]
    rw [<- mul_assoc]
    rfl

Conclusion
"
My proof:
```
 cases h1 with d hd
    use d
    rw [hd]
    rw [mul_assoc,mul_comm d c]
    rw [<- mul_assoc]
    rfl
```
"
