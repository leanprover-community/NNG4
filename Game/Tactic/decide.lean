import Game.Tactic.LabelAttr
import Game.MyNat.Definition

-- to get numerals of type MyNat to reduce to MyNat.succ (MyNat.succ ...)
@[MyNat_decide]
theorem ofNat_succ : (OfNat.ofNat (Nat.succ n) : ℕ) = MyNat.succ (OfNat.ofNat n) := _root_.rfl


/- modified `decide` tactic which first runs a custom
simp call to reduce numerals like `1 + 1` to
`MyNat.succ (MyNat.succ MyNat.zero)
-/
macro "decide" : tactic => `(tactic|(
  try simp only [MyNat_decide]
  try decide
))
