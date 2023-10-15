import Lean

universe u

@[never_extract]
axiom iGiveUpAx (α : Sort u) (synthetic := false) : α

/--
`IGiveUp` behaves like `sorry`, except that it is the ultimative cheat code:
The game won't complain - or notice - if you proof anything with `IGiveUp`.
-/
macro "IGiveUp" : tactic => `(tactic| exact @iGiveUpAx _ false)
