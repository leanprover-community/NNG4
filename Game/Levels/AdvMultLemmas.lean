-- import Game.Levels.AdvMultiplication


namespace MyNat

LemmaDoc MyNat.mul_one_eq_one as "mul_one_eq_one" in "*" "
`mul_one_eq_one c d` is a proof that `c * d = 1 → c = 1`.
"
NewLemma MyNat.mul_one_eq_one


Statement
    (c d : ℕ) (h : c * d = 1) : c = 1 := by
  have foo : c ≤ 1 := by
    rw [← h]
    apply le_mul_right
    rw [h]
    symm
    apply zero_ne_succ
  apply le_one at foo
  cases foo with h0 h1
  · rw [h0, zero_mul] at h
    apply zero_ne_succ at h
    contradiction
  exact h1
