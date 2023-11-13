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

#check Nat.div
#check Nat.sub
#check Nat.lt
#check Nat.mod


def pred : ℕ → ℕ
  | zero => zero
  | succ a => a

def sub : ℕ → ℕ → ℕ
  | a, zero => a
  | a, succ b => pred (sub a b)

def lt (m n : ℕ) : Prop :=
  MyNat.le (succ n) m

instance : LT MyNat where
  lt := MyNat.lt

instance : Sub MyNat where
  sub := MyNat.sub

def mod : ℕ → ℕ → ℕ
  | 0, _ => 0
  | a@(_ + 1), b => mod a b

#eval mod 4 3

def div (x y : ℕ) : ℕ :=
  if 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0


def f (x : ℕ) :=
  match x % 2 with
  |0 => x / 2
  |1 => 3 * x + 1
