namespace Straume.Pos

structure Pos where
  i : Nat
  deriving DecidableEq, Repr, BEq, Ord

instance : HAdd Pos Pos Pos where
  hAdd x y := ⟨ x.i + y.i ⟩
