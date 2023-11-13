import Game.Levels.Hard

World "Hard"
Level 1
Title "FLT"

LemmaTab "Hard"

namespace MyNat

Introduction
"
  We beign with a problem which has been proven, Fermat's Last Theorem.
"

LemmaDoc MyNat.FLT as "FLT" in "Hard" "
`FLT` is the proof of Fermat's Last Theorem
"

Statement FLT
  (n a b c : ℕ) (hn : 2 ≤ n) : a^n + b^n = c^n → a * b * c = 0 := by
  sorry



end MyNat
