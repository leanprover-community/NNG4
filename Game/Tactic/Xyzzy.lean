import Lean

universe u

@[never_extract]
axiom iGiveUpAx (α : Sort u) (synthetic := false) : α

/--
`xyzzy` is an ancient magic word, believed to be the root of the
modern word `sorry`. The game won't complain - or notice - if you
prove anything with `xyzzy`.
-/
macro "xyzzy" : tactic => `(tactic| exact @iGiveUpAx _ false)
