
/--import Game.Levels.AdvMultiplication
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
    (a b : ℕ) (h : a ∣ b ∧ b ∣ a): a = b := by
  Hint "You will need to expand what `h1` and `h2` actually mean. You may find `cases` helpful."
  cases h with h1 h2
  cases h1 with m hm
  cases h2 with n hn
  sorry--/
