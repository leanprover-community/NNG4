import Game.Levels.Addition.Level_6 -- makes simps work?
import Mathlib.Tactic
namespace MyNat

/-

# Bonus Peano Axioms level

If this becomes a level:

Explain that Peano had two extra axioms:

succ_inj (a b : ℕ) :
  succ a = succ b → a = b

zero_ne_succ (a : ℕ) :
  zero ≠ succ a

In Lean we don't need these axioms though, because they
follow from Lean's principles of reduction and recursion.

Principle of recursion: if two things are true:
* I know how to do it for 0
* Assuming (only) that I know how to do it for n.
  I know how to do it for n+1.

Note the "only".

-/

@[simp] def pred : ℕ → ℕ
| 0 => 37
| n + 1 => n

theorem pred_succ : pred (succ n) = n := by simp
/-

## pred

pred(x)=x-1, at least when x > 0. If x=0 then there's no
answer so we just let the answer be a junk value because
it's the simplest way of dealing with this case.
If a mathematician asks us what pred of 0 is, we tell
them that it's a stupid question by saying 37, it's
like a poo emoji. But Peano was a cultured mathematician
and this proof of `succ_inj` will only use `pred` on
positive naturals, just like today's cultured mathematician
never divides by zero.

We need to learn how to deal wiht a goal of the form `P → Q`

-/

theorem succ_inj (a b : ℕ) (h : succ a = succ b) : a = b := by
  apply_fun pred at h
  simpa

/-

These proofs are now broken because pred_succ isn't rfl
any more

-- this is beautiful stuff and the fact that it doesn't work now is
-- one reason why this is not becoming a level I think
theorem succ_inj' (a b : ℕ) : a.succ = b.succ → a = b := by
  intro h
  --apply_fun pred at h
  have this := congrArg pred h
  -- `exact` works up to definitional equality, and
  -- pred (succ n) = n is true *by definition*
  -- (this is why the proof is `rfl`)
  exact h -- now has started failing


lemma succ_inj'' (a b : ℕ) : a.succ = b.succ → a = b := by
  intro h
  -- `apply_fun` is just a wrapper for congrArg.
  -- congrArg : (f : α → β) (h : a₁ = a₂) : f a₁ = f a₂
  -- This is a fundamental property of equality.
  -- You prove it by induction on equality, by the way.
  -- But that's a story for another time.
  apply congrArg pred h

-- functional programming point of view: the proof is just
-- a function applied to a function whose output
-- is another function.
lemma succ_inj''' (a b : ℕ) : succ a = succ b → a = b :=
congrArg pred

-/
@[simp] theorem succ_eq_succ_iff : succ a = succ b ↔ a = b := by
  constructor
  · exact succ_inj a b
  · simp

/-
## zero_ne_succ

zero_ne_succ (a : ℕ) :
  zero ≠ succ a

What does `≠` even *mean*?

By *definition*, `zero ≠ succ a` *means* `zero = succ a → false`

-/

open Bool

@[simp] def isZero : ℕ → Bool
| 0 => true
| (_ + 1) => false

example : true ≠ false := by simp

example : isZero 0 = true := by simp
example : isZero (succ n) = false := by simp

theorem zero_ne_succ (n : ℕ) : 0 ≠ succ n := by
  by_contra h -- nice tactic to teach
  -- apply_fun would be another one
  have h := congrArg isZero h
  simp at h

theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 := by
  by_contra h
  have h := congrArg isZero h
  simp at h

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
