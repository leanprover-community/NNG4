import Game.Levels.AdvMultiplication
import Game.MyNat.Division

World "Division"
Level 9
Title "dvd_add_right"

TheoremTab "∣"

namespace MyNat

Introduction
"
 We will prove that if d ∣ a , and d ∣ b, then we know that d ∣ a + b.
"

/-- div_add_right d a b ` is a proof that `d ∣ a ∧ d ∣ b` then ` d ∣ a + b`.-/
TheoremDoc MyNat.dvd_add_right as "dvd_add_right" in "∣"


Statement dvd_add_right
    (d a b : ℕ)  (ha : d ∣ a) (hab : d ∣ b) : d ∣ a + b := by
  cases ha with n hn
  cases hab with m hm
  use n + m
  rw[hn,hm]
  rw[mul_add]
  rfl
