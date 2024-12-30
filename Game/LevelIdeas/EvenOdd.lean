-- EvenOdd World.
-- This entire world revolves around `∃ (t : ℕ), t + t = n` and `∃` is only
-- introduced in `≤ world` so this needs to go after `≤ world`
-- Furthermore this level is just *painful* (i.e. not actually fun) with no `decide` or `simp_add`
-- so it should also require algorithm world
-- Authors of levels: Kevin Buzzard and Ivan Farabella
import Game.Levels.LessOrEqual
import Game.Levels.Algorithm

namespace MyNat

-- Put this in `Game/MyNat/EvenOdd.lean`. See for example `Game/MyNat/LE.lean`
-- for how to set up a new concept.
def IsEven (n : ℕ) := ∃ (t : ℕ), t + t = n

-- Put this in `Game/MyNat/EvenOdd.lean` too, and present it to users
-- as a definition.
theorem isEven_def (n : ℕ) : IsEven n ↔ ∃ t, t + t = n := Iff.rfl

-- level 1
theorem isEven_zero : IsEven 0 := by
  rw [isEven_def]
  use 0
  decide

-- level 2
theorem isEven_two : IsEven 2 := by
  rw [isEven_def]
  use 1
  decide

-- level 3
theorem isEven_add_isEven (a b : ℕ) (ha : IsEven a) (hb : IsEven b) : IsEven (a + b) := by
  rw [isEven_def] at *
  cases ha with r hr
  cases hb with s hs
  use r + s
  rw [← hr, ← hs]
  simp_add

-- should also be in `Game/MyNat/EvenOdd.lean` but only unlocked
def IsOdd (n : ℕ) : Prop := ∃ t : ℕ, t + t + 1 = n

-- given to the user
theorem isOdd_def (n : ℕ) : IsOdd n ↔ ∃ t : ℕ, t + t + 1 = n := Iff.rfl

-- level 4
theorem isOdd_one : IsOdd 1 := by
  rw [isOdd_def]
  use 0
  decide

-- level 5
theorem not_isOdd_zero : ¬ IsOdd 0 := by
  by_contra h
  rw [isOdd_def] at h
  cases h with t ht
  -- this strat probably needs hints
  rw [← succ_eq_add_one] at ht
  apply succ_ne_zero at ht
  exact ht

-- level 6
theorem isOdd_add_isOdd {a b : ℕ} (ha : IsOdd a) (hb : IsOdd b) : IsEven (a + b) := by
  rw [isOdd_def, isEven_def] at *
  cases ha with r hr
  cases hb with s hs
  use r + s + 1
  rw [← hr, ← hs]
  simp_add

-- level 7
theorem isEven_add_isOdd {a b : ℕ} (ha : IsEven a) (hb : IsOdd b) : IsOdd (a + b) := by
  rw [isOdd_def, isEven_def] at *
  cases ha with r hr
  cases hb with s hs
  use r + s
  rw [← hr, ← hs]
  simp_add

-- level 8
theorem IsOdd_add_IsEven (a b : ℕ) (ha : IsOdd a) (hb : IsEven b) : IsOdd (a + b) := by
  -- tell them this trick to save time
  rw [add_comm]
  apply isEven_add_isOdd
  · exact hb
  · exact ha

-- level 9
@[simp] theorem isOdd_succ_iff (a : ℕ) : IsOdd (succ a) ↔ IsEven a := by
  rw [isEven_def, isOdd_def]
  constructor
  · rintro ⟨t, ht⟩
    use t
    apply succ_inj
    rwa [succ_eq_add_one]
  · rintro ⟨s, rfl⟩
    use s
    rw [succ_eq_add_one]
    rfl

-- level 10
-- this is harder because there's a case split in the => direction
@[simp] theorem isEven_succ_iff (a : ℕ) : IsEven (succ a) ↔ IsOdd a := by
  rw [isEven_def, isOdd_def]
  constructor
  · rintro ⟨t, ht⟩
    -- This trick was taught in advanced addition world level 5
    cases t with d
    · -- ht is now false
      rw [add_zero] at ht
      apply zero_ne_succ at ht
      cases ht
    · -- this is tricky, probably needs guidance
      rw [add_succ] at ht
      apply succ_inj at ht
      use d
      rw [← ht]
      rw [succ_eq_add_one]
      simp_add
  · rintro ⟨s, rfl⟩
    use s + 1
    rw [succ_eq_add_one]
    simp_add

-- Boss level comes in two parts: we have to prove that every number
-- is exactly one of even and odd!

-- level 11
theorem isEven_or_isOdd (n : ℕ) : IsEven n ∨ IsOdd n := by
  induction n with d hd
  · left
    exact isEven_zero
  · -- tell them that isEven_succ_iff and isOdd_succ_iff are simp lemmas
    simp
    -- tell them that it's now pure logic
    tauto -- oh no! This is not taught until advanced multiplication world!

-- level 12
theorem not_isEven_and_isOdd (n : ℕ) : ¬ (IsEven n ∧ IsOdd n) := by
  induction n with d hd
  · by_contra h
    cases h with h1 h2
    -- how should we be teaching this?
    apply not_isOdd_zero at h2
    exact h2
  · -- again cancel the succs
    simp
    -- and then it's logic, but this is hard to spot
    tauto


/-

After multiplication world (which we never used here) there are more
tedious levels e.g.

IsOdd_mul_IsOdd,
`IsEven a → IsEven (a * b)` etc
-/

end MyNat
