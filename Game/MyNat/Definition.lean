import Game.Tactic.LabelAttr -- MyNat_decide attribute

/-- Our copy of the natural numbers called `MyNat`, with notation `ℕ`. -/
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat
-- deriving BEq, DecidableEq, Inhabited

@[inherit_doc]
notation (name := MyNatNotation) (priority := 1000000) "ℕ" => MyNat
-- Note: as long as we do not import `Mathlib.Init.Data.Nat.Notation` this is fine.

namespace MyNat

instance : Inhabited MyNat where
  default := MyNat.zero

@[MyNat_decide]
def ofNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero   => MyNat.zero
  | Nat.succ b => MyNat.succ (ofNat b)

@[MyNat_decide]
def toNat (x : MyNat) : Nat :=
  match x with
  | MyNat.zero   => Nat.zero
  | MyNat.succ b => Nat.succ (toNat b)

instance instofNat {n : Nat} : OfNat MyNat n where
  ofNat := ofNat n

instance : ToString MyNat where
  toString p := toString (toNat p)

@[MyNat_decide]
theorem zero_eq_0 : MyNat.zero = 0 := rfl

def one : MyNat := MyNat.succ 0

-- TODO: Why does this not work here??
-- We do not want `simp` to be able to do anything unless we unlock it manually.
attribute [-simp] MyNat.succ.injEq

theorem eq_toNat_eq : ∀ (m n : MyNat), m.toNat = n.toNat → m = n
  | zero, zero, _ => rfl
  | succ m, succ n, h => congrArg succ $ eq_toNat_eq m n (Nat.succ.inj h)
