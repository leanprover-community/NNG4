import Game.Metadata
import Game.MyNat.Addition


World "AdvProposition"
Level 3
Title "and_trans"

open MyNat

Introduction
"
Here is another exercise to `rcases` and `constructor`.
"

/-- If $P$, $Q$ and $R$ are true/false statements, then $P \land Q$ and
$Q \land R$ together imply $P \land R$. -/
Statement --and_trans
    (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R := by
  Hint "Here's a trick:

  Your first steps would probably be
  ```
  intro h
  rcases h with ⟨p, q⟩
  ```
  i.e. introducing a new assumption and then immediately take it apart.

  In that case you could do that in a single step:

  ```
  intro ⟨p, q⟩
  ```
  "
  intro hpq
  rcases hpq with ⟨p, q⟩
  intro hqr
  rcases hqr with ⟨q', r⟩
  constructor
  exact p
  exact r

Conclusion
"

"
