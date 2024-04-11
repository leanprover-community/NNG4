import Game.Tactic.Rw
--import Game.MyNat.Multiplication

example (a b : Nat) : a * b = b * a := by
  rewrite [mul_comm]

example (a b : Nat) : a * b = b * a := by
  rw [mul_comm]

example (a b : MyNat) : a * b = b * a := by
  rewrite [mul_comm]

example (a b : Nat) : a * b = b * a := by
  reewrite [mul_comm]
