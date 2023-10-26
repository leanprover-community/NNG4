import Game.Levels.Addition
import Game.Levels.Implication

-- first let's remind ourselves how fiddly this is.

namespace MyNat

lemma add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a, add_assoc]
  rfl

-- two problems: brackets and commutativity. Looking only at the
-- letters, we see that we can change LHS into RHS by swapping c,d
-- and then swapping b,d. Brackets make this awkward. But add_comm
-- and add_left_comm in
example (a b c d : ℕ) : a + (b + c) + d = a + d + (b + c) := by
  repeat rw [add_assoc]
  rw [add_comm c]
  rw [add_left_comm b]
  rfl

-- macro_rules | `(tactic| ac_rfl) => `(tactic| simp only [add_assoc, add_left_comm, add_comm])


-- now let's make a new tactic
example (a b c d e f g h : ℕ) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_assoc, add_comm, add_left_comm]
  -- tada

def is_zero : ℕ → Prop
| 0 => True
| succ n => False

-- put somewhere where rfl isn't broken?
lemma is_zero_zero : is_zero 0 = True := by
  change True = True
  rfl

-- put somewhere where rfl isn't broken?
lemma is_zero_succ (n : ℕ) : is_zero (succ n) = False := by
  change False = False
  rfl

example (n : ℕ) : (0 : ℕ) ≠ succ n := by
  intro h
  apply_fun is_zero at h
  rw [is_zero_zero, is_zero_succ] at h
  contradiction

def pred : ℕ → ℕ
| 0 => 37
| succ n => n

-- put somewhere where rfl isn't broken?
lemma pred_succ (n : ℕ) : pred (succ n) = n := by
  change n = n
  rfl

example (a b : ℕ) (h : succ a = succ b) : a = b := by
  apply_fun pred at h
  rw [pred_succ, pred_succ] at h
  exact h

instance instDecidableEq : DecidableEq MyNat := fun (a b : MyNat) =>
match a, b with
| 0, 0 => isTrue <| by

  show 0 = 0
  rfl

| 0, succ q => isFalse <| by

  show 0 ≠ succ q
  exact zero_ne_succ q

| succ p, 0 => isFalse <| by

  show succ p ≠ 0
  symm
  exact zero_ne_succ p

| succ p, succ q =>
  match instDecidableEq p q with
  | isTrue (h : p = q) => isTrue <| by

    show succ p = succ q
    rw [h]
    rfl

  | isFalse (h : p ≠ q) => isFalse <| by

    show succ p ≠ succ q
    intro h2
    apply succ_inj at h2
    contradiction

example : (20 : ℕ) + 20 = 40 := by decide

example : (20 : ℕ) + 20 ≠ 41 := by decide

-- example : (20 : ℕ) * 20 = 400 := by decide
/-
example : (200 : ℕ) + 200 = 400 := by decide
-/
