import Mathlib.Tactic
import Nng4.NNG

/-

Tactics this needs: `intro` (could be removed if
required, only ever the first line in a tactic,
-/
/-

# Bonus Peano Axioms level

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

#check Nat.succ
-- example of a definition by recursion
def double : ℕ → ℕ 
| 0 => 0
| (n + 1) => 2 + double n

theorem double_eq_two_mul (n : ℕ) : double n = 2 * n := by
  induction' n with d hd -- need hacked induction' so that it gives `0` not `Nat.zero`
  show 0 = 2 * 0 -- system should do this
  norm_num -- needs to be taught
  show 2 + double d = 2 * d.succ
  rw [hd]
  rw [Nat.succ_eq_add_one] -- `ring` should do this
  ring-- 

-- So you're happy that this is a definition by recursion
def f : ℕ → ℕ
| 0 => 37
| (n + 1) => (f n * 42 + 691)^2

-- So you're happy that this is a definition by recutsion
def pred : ℕ → ℕ
| 0 => 37
| (n + 1) => n

lemma pred_succ : pred (n.succ) = n := 
rfl -- true by definition
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

lemma succ_inj (a b : ℕ) : a.succ = b.succ → a = b := by
  -- assume `a.succ=b.succ`
  intro this
  -- apply pred to both sides
  apply_fun pred at this
  -- pred and succ cancel by lemma `pred_succ`
  rw [pred_succ, pred_succ] at this
  -- and we're done
  exact this

lemma succ_inj' (a b : ℕ) : a.succ = b.succ → a = b := by
  intro h
  apply_fun pred at h
  -- `exact` works up to definitional equality, and
  -- pred (succ n) = n is true *by definition*
  -- (this is why the proof is `rfl`)
  exact h

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
lemma succ_inj''' (a b : ℕ) : a.succ = b.succ → a = b := 
congrArg pred


/-
Poss boring
## Interlude ; 3n+1 problem

unsafe def collatz : ℕ → ℕ
| 0 => 37
| 1 => 37
| m => if m % 2 = 0 then collatz (m / 2) else collatz (3 * m + 1)     


-- theorem proof_of_collatz_conjecture : ∀ n, ∃ (t : ℕ), collatz ^ t n = 1 := by
--  sorry

Here is a crank proof I was sent of the 3n+1
problem. Explanaiton of problem. Proof: By induction.
Define f(1)=stop. 
Got to prove that for all n, it terminates.

For even numbers this is obvious so they're all done. 
For odd numbers, if n is odd then 3n+1 is even, but
as we already observed it's obvious for all even numbers,
so we're done.

## zero_ne_succ

zero_ne_succ (a : ℕ) :
  zero ≠ succ a

What does `≠` even *mean*?

By *definition*, `zero ≠ succ a` *means* `zero = succ a → false`

-/

def is_zero : ℕ → Bool
| 0 => Bool.true
| (n + 1) => Bool.false

lemma is_zero_zero : is_zero 0 = true := rfl
lemma is_zero_succ : is_zero (n + 1) = false := rfl

lemma zero_ne_succ (n : ℕ) : 0 ≠ n.succ := by
  by_contra h
  
  intro this
  apply_fun is_zero at this
  rw [is_zero_zero, is_zero_succ] at this
  cases this -- splits into all the cases where this is true





