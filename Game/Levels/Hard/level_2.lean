import Game.Levels.Hard.level_1


World "Hard"
Level 2
Title "Collatz"

LemmaTab "Hard"

namespace MyNat

Introduction
"
  The next problem we will look at has not been solved. It is the Collatz conjecture.
  If we define a function f such that f(n) = n / 2 if n is even, and 3n + 1 if it is odd,
  the conjecture states that succesivley applying will eventually result in 1, regardless
  of the starting point, n. For instance, if n = 5, the sequence goes: 5, 16, 8, 4, 2, 1.
  Once the sequence reaches 1, it gets stuck in a cycle of 1, 4, 2, 1, 4, 2, 1, ... forever.
"

LemmaDoc MyNat.Colatz as "Collatz" in "Hard" "
`Collatz` is the proof of disproof of the Collatz conjecture.
"

def even (n : ℕ) : Prop
  | zero => true
  | succ a => ¬ (even a)

def half (n : ℕ) :=
  | zero => zero
  | succ a =>
  match even a with
  | true => half a + 1
  | false => half a

-- 'collatz function'
def f (x : ℕ) :=
  match even x with
  | true => half n
  | false => 3 * n + 1

-- kᵗʰ collatz term stariting at n
def collatz (n k : ℕ) :=
  match k with
  | zero => f n
  | succ b => f (collatz n b)


Statment Collatz : ∀ (n : ℕ), ∃ (k : ℕ), collatz n k = 1 := by
  sorry


#eval half 4
