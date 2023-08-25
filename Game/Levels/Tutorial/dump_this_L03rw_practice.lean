import Game.Metadata
import Game.MyNat.Multiplication
 import Game.MyNat.Power


World "Tutorial"
Level 3
Title "rw practice"

Introduction
"
In this level we have three hypotheses `hap : a = p`, `hbq : b = q` and `hcr : c = r`.
Use the `rw` tactic to prove that $ab + 2bc^3 + 7 = pq + 2qr^3 + 7$. Remember that `rw` eats
*proofs*, not *statements*.

Here are some more facts about `rw`.

* `rw` can take more than one proof at a time. For example try `rw [hap, hcr]`.

* If `h` is a proof of `X = Y`, then `rw [h]` changes *all* `X`s in the goal to `Y`s.

* If you want to change all `Y`s to `X`s, then try `rw [←h]`. Get the back-arrow by
  typing `\\l` (`l` for left).
"

/-- If $a=p$, $b=q$ and $c=r$, then $ab+2c^3+7=pq+2r^3+7.$ -/
Statement (a b c p q r : ℕ) (hap : a = p) (hbq : b = q) (hcr : c = r) :
    a * b + 2 * b * c ^ 3 + 7 = p * q + 2 * q * r ^ 3 + 7 := by
  Hint "Switch to editor mode if you want to experiment with `rw` more easily.
        Note that each tactic needs to start at the beginning of a line."
  rw [hap, hbq, hcr]
  Hint "If you didn't already, try going to editor mode, proving this
  theorem with `rw [hap, hbq, hcr]` and then clicking around the commas"
  rfl

Conclusion
"
In editor mode, you can click around the proof and see the state of Lean's brain at
any point in the proof.
You can also edit your proof and experiment more with it.
There is no need to use editor mode, especially if you just want to beat
the final boss.
"
