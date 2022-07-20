import Straume.Prob
import Straume.Prob.Ordering

/-
Orderings between things such that if two things are incomparable, that's for certain, whereas if two things are comparable, that may or may not be true.
For an example of a practical application of one such orderin, check out bloom filters and, subsequently bloom clocks.
-/
namespace Straume.Prob.Ordering.MaybeComparable

open Straume.Prob.Ordering
open Straume.Prob.FalsePositive

class MCPartial (α : Type u) [BEq α] where
  lt : α → α → PSum Incomparable FalsePositive
  le : α → α → PSum Incomparable FalsePositive :=
    fun x y => match lt x y with
               | .inl _ => PSum.inl Incomparable.mk
               | .inr z => PSum.inr $ assure z (forSure $ BEq.beq x y)
  compare : α → α → Comparison FalsePositive :=
    fun x y => match le x y with
               | .inl _ => .incomparable
               | .inr .no => match le y x with
                             | .inl _ => .incomparable
                             | .inr .no => .eq
                             | .inr z => .gt z
               | .inr z => .lt z