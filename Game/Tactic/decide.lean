/- modified `decide` tactic which first runs a custom
simp call to reduce numerals like `1 + 1` to
`MyNat.succ (MyNat.succ MyNat.zero)
-/

macro "decide" : tactic => `(tactic|(
  try simp only [MyNat_decide]
  try decide
))
