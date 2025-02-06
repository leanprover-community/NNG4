import Game.Metadata
import Game.MyNat.LE
import Game.MyNat.LT
import Game.Tactic.Use
import Game.Levels.AdvAddition

World "LessThan"
Level 1
Title "LessThan is irreflexive"

namespace MyNat


/-- `a < b` is *notation* for `succ a ≤ b`, and 'succ a ≤ b` in turn
is *notation* for `∃ c : b = succ a + c`.  This mean that if you have
a *goal* of the for `a < b`, you can make progress with the `use
tactice`, and if you have a *hypothesis* (h : a < b) you can make
progress with `cases h with c hc`.  -/ 
DefinitionDoc LT as "<"

Introduction "In the `≤` world, we showed that `≤` is reflexive
relation.  In this world our first task is to show that ̀`<` is an
*ir*reflexive relation.  An irreflexive relation is one for which no
element is related to itself.

Remember that `a<b` is notation for `succ a ≤ b`, And that `succ a ≤
b` is itself notation for \"there exists `c` such that `b = succ a +
c`\".  As such, we can make progress on goals of the form `a < b` by
`use`ing the number which is morally `b - succ a' (i.e. `use b - succ
a`).

Of course we haven't defined subtraction so deciphering which
expression is morally the difference will be your task."

/--`lt_irrefl a` is a proof that `¬(a < a)`.  In words, a natural
number `a` is not less than itself.-/
TheoremDoc MyNat.lt_irrefl as "lt_irrefl" in "<"

/-- If $x$ is a natural number, then $\neg (x \lt x)$. -/
Statement lt_irrefl (x : ℕ) : ¬(x < x) := by
  intro h0
  Hint "You should probably split the hypothesis with a `cases`."
  cases h0 with n h1
  Hint "Aiming for a contradiction, can you show that this implies that `succ {n} = 0`?
  If you get stuck you can ask for an additional hint."
  Hint (hidden := true) "Either `add_right_eq_self` or `add_left_eq_self` might be helpful."

  rw [MyNat.succ_add] at h1
  rw [←MyNat.add_succ] at h1
  have h2 := MyNat.add_right_eq_self x (succ n) h1.symm

  Hint "`succ_ne_zero` might be helpful."
  have h3 := succ_ne_zero n
  exact h3 h2

TheoremTab "<"

Conclusion "Nice job, click the \"Next\" button to continue."
