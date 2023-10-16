World "Division"
Level 5
Title "div_a_div_ab"

Introduction
"
  In this section, we will prove that if d ∣ a, then d ∣ ab.
"


Statement
    (d a b : ℕ) (hd : d ∣ a) : d ∣ (a * b) := by
  match hd with
  |⟨k, hk⟩ =>
  -- a = kd
  use (k * b)
  -- do some commuting
  -- should be easy from then on

Conclusion
"
  
"
