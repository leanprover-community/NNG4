/-
Copyright Ivan
Authors Kevin Buzzard and Ivan
-/
import Game.Levels.Addition
--import Game.MyNat.DecidableEq

namespace MyNat

def IsEven (n : ℕ) := ∃ (t : ℕ), t + t = n

theorem isEven_def (n : ℕ) : IsEven n ↔ ∃ t, t + t = n := Iff.rfl

theorem isEven_zero : IsEven 0 := by
  rw [isEven_def]
  use 0 -- new tactic: eliminate ∃
  rw [add_zero]
  rfl
--  or `decide`

theorem isEven_two : IsEven 2 := by
  rw [isEven_def]
  use 1
  -- this is tedious without `decide`
  rw [two_eq_succ_one, one_eq_succ_zero, add_succ, add_zero]
  rfl
  -- `decide` is surely better

theorem not_isEven_one : ¬ IsEven 1 := by -- ¬ is new
  rw [isEven_def]  -- ne_def is new
  -- want push_neg
  rw [not_exists]
  intro t
  cases t with d
  sorry -- should be `decide`
  intro h
  rw [one_eq_succ_zero, add_succ] at h
  by_contra h
  rw [one_eq_succ_zero, add_succ, succ_eq_succ_iff, succ_add] at h
  simp_all [succ_ne_zero]

theorem isEven_add_isEven (a b : ℕ) (ha : IsEven a) (hb : IsEven b) : IsEven (a + b) := by
  simp_all only [isEven_def]
  rcases ha with ⟨r, rfl⟩ -- great chance to introduce rcases rfl, esp to avoid [← hr]
  rcases hb with ⟨s, rfl⟩
  use r + s
  simp only [add_assoc, add_left_comm, add_comm]
  ac_rfl
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
  simp -- not ideal
  -- `decide` better

theorem not_isOdd_zero : ¬ IsOdd 0 := by
  by_contra h
  rw [isOdd_def] at h
  rcases h with ⟨t, ht⟩
  rw [← succ_eq_add_one] at ht
  symm at ht
  apply zero_ne_succ at ht
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
    rcases h with ⟨-, h0O⟩
    revert h0O
    exact not_isOdd_zero
  · simp
    tauto

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
