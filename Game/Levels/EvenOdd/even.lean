import Game.Levels.Addition.Level_5
import Game.Tactic.Use
import Game.Levels.Logic.bonus_peano_axiom_levels

namespace MyNat

-- this should be in logic
instance instDecidableEq : DecidableEq MyNat := fun (a b : MyNat) =>
match a with
| 0 => match b with
  | 0 => isTrue (by simp)
  | succ q => isFalse (by simp [zero_ne_succ])
| succ p => match b with
  | 0 => isFalse (by simp [succ_ne_zero])
  | succ q =>
      match instDecidableEq p q with
      | isTrue h => isTrue <| by simp_all
      | isFalse h => isFalse <| by simp_all

  -- this should be somewhere else
-- first the important lemma
-- this should be in addition world after associativity
-- Stress that now you have commutativity and associativity, you don't need
-- to do any more induction, it's all about rewriting.
-- `add_left_comm` is part of a great algorithm which will prove boring identities
theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a, add_assoc]
  rfl

-- no need for this now
theorem add_add_add_comm (a b c d : ℕ) : (a + b) + (c + d) = (a + c) + (b + d) := by
  simp only [add_assoc, add_left_comm, add_comm]

example (a b c d e f g h : ℕ) :
    (b + (f + e)) + (a + c + (h + g + d)) = a + b + c + d + e + f + g + h := by
  simp only [add_assoc, add_left_comm, add_comm]

def IsEven (n : ℕ) := ∃ (t : ℕ), t + t = n

theorem isEven_def (n : ℕ) : IsEven n ↔ ∃ t, t + t = n := Iff.rfl

theorem isEven_zero : IsEven 0 := by
  rw [isEven_def]
  use 0 -- new tactic: eliminate ∃
  decide

theorem isEven_two : IsEven 2 := by
  rw [isEven_def]
  use 1
  decide

theorem not_isEven_one : ¬ IsEven 1 := by -- ¬ is new
  rw [isEven_def]  -- ne_def is new
  -- want push_neg
  rw [not_exists]
  intro t
  induction t with d hd
  decide
  clear hd
  by_contra h
  rw [one_eq_succ_zero, add_succ, succ_eq_succ_iff] at h
  simp_all [succ_ne_zero]

theorem isEven_add_isEven (a b : ℕ) (ha : IsEven a) (hb : IsEven b) : IsEven (a + b) := by
  simp_all only [isEven_def]
  rcases ha with ⟨r, rfl⟩ -- great chance to introduce rcases rfl, esp to avoid [← hr]
  rcases hb with ⟨s, rfl⟩
  use r + s
  simp only [add_assoc, add_left_comm, add_comm]

/-

After we have multiplication
`(ha: IsEven a) : IsEven ( a * b )`
and the other way

-/


def IsOdd (n : ℕ) : Prop := ∃ t : ℕ, t + t + 1 = n

theorem isOdd_def (n : ℕ) : IsOdd n ↔ ∃ t : ℕ, t + t + 1 = n := Iff.rfl

theorem isOdd_one : IsOdd 1 := by
  rw [isOdd_def]
  use 0
  decide

theorem not_isOdd_zero : ¬ IsOdd 0 := by
  by_contra h
  rw [isOdd_def] at h
  rcases h with ⟨t, ht⟩
  rw [← succ_eq_add_one] at ht
  revert ht
  apply succ_ne_zero

-- theorems about succ_even etc here

@[simp] theorem isOdd_succ_iff (a : ℕ) : IsOdd (succ a) ↔ IsEven a := by
  rw [isEven_def, isOdd_def]
  constructor
  · rintro ⟨t, ht⟩
    use t
    apply succ_inj
    rwa [succ_eq_add_one]
    done
  · rintro ⟨s, rfl⟩
    use s
    rw [succ_eq_add_one]
    rfl

@[simp] theorem isEven_succ_iff (a : ℕ) : IsEven (succ a) ↔ IsOdd a := by
  rw [isEven_def, isOdd_def]
  constructor
  · rintro ⟨t, ht⟩
    induction t with d _
    · simp_all [zero_ne_succ]
    · rw [add_succ, succ_eq_succ_iff] at ht
      use d
      rw [← ht, succ_eq_add_one]
      simp only [add_assoc, add_left_comm, add_comm]
  · rintro ⟨s, rfl⟩
    use s + 1
    rw [succ_eq_add_one]
    simp only [add_assoc, add_left_comm, add_comm]
    done

theorem isEven_or_isOdd (n : ℕ) : IsEven n ∨ IsOdd n := by
  induction n with d hd
  · left
    exact isEven_zero
  · simp
    -- need tauto
    rcases hd with (hdE | hdO) <;> simp_all

theorem not_isEven_and_isOdd (n : ℕ) : ¬ (IsEven n ∧ IsOdd n) := by
  induction n with d hd
  · by_contra h
    rcases h with ⟨h0E, h0O⟩
    revert h0O
    exact not_isOdd_zero
  · simp
    -- desperately need tauto
    sorry

theorem isOdd_add_isOdd {a b : ℕ} (ha : IsOdd a) (hb : IsOdd b) : IsEven (a + b) := by
  rw [isOdd_def, isEven_def] at *
  rcases ha with ⟨r, rfl⟩
  rcases hb with ⟨s, rfl⟩
  use r + s + 1
  simp only [add_assoc, add_left_comm, add_comm]

theorem IsEven_add_IsOdd( a b : ℕ ) (ha : IsEven a) (hb : IsOdd b) : IsOdd ( a + b ) := by
  rw [isOdd_def, isEven_def] at *
  rcases ha with ⟨r, rfl⟩
  rcases hb with ⟨s, rfl⟩
  use r + s
  simp only [add_assoc, add_left_comm, add_comm]
  done

theorem IsOdd_add_IsEven( a b : ℕ ) (ha : IsOdd a) (hb : IsEven b) : IsOdd ( a + b) := by
  rw [isOdd_def, isEven_def] at *
  rcases ha with ⟨r, rfl⟩
  rcases hb with ⟨s, rfl⟩
  use r + s
  simp only [add_assoc, add_left_comm, add_comm]


/-

After multiplication:

IsOdd_mul_IsOdd

-/
end MyNat
