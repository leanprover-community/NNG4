import Game.Levels.AdvMultiplication.L01mul_le_mul_right

World "AdvMultiplication"
Level 2
Title "mul_left_ne_zero"

TheoremTab "*"

namespace MyNat

/-- `mul_left_ne_zero a b` is a proof that `a * b ≠ 0 → b ≠ 0`. -/
TheoremDoc MyNat.mul_left_ne_zero as "mul_left_ne_zero" in "*"

Introduction
"If you have completed Algorithm World then you can use the `contrapose!` tactic
here. If not then I'll talk you through a manual approach."

Statement mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  Hint "We want to reduce this to a hypothesis `b = 0` and a goal `a * b = 0`,
  which is logically equivalent but much easier to prove. Remember that `X ≠ 0`
  is notation for `X = 0 → False`. Click on `Show more help!` if you need hints."
  Hint (hidden := true) "Start with `intro hb`."
  intro hb
  Hint (hidden := true) "Now `apply h` and you can probably take it from here."
  apply h
  rw [hb, mul_zero]
  rfl
