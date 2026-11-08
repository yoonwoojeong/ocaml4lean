/-
Regression test: the kernel numbers the auxiliary types of a nested inductive in
the order it meets nested occurrences (domain before body).  `Box2.mk` has an
`Option α` field before a `List α` field, so the auxiliary type for `Option T`
must come before the one for `List T`, and the recursors `T.rec_1`, `T.rec_2`, …
must follow that order.  (Found on Lean's own `Lean.Elab.InfoTree`.)
-/
structure Box2 (α : Type) where
  fst : Option α
  snd : List α

inductive T where
  | leaf : T
  | mk : Box2 T → T

structure Box3 (α : Type) where
  a : Array α
  b : Option (List α)
  c : List α

inductive U where
  | mk : Box3 U → Option U → U
