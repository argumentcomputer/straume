import Straume.Prob.Ordering

namespace Straume.Clock

/- Typeclasses to work with logical clocks.
-/

open Straume.Prob.Ordering.Comparable.FalsePositive
  renaming Partial → FP.Partial

-- open Straume.Prob.Ordering.Comparable
--   renaming Comparison → P.Comparison

open Straume.Prob (FalsePositive)
open Straume.Prob.FalsePositive (forSure)

universe u
universe v
universe s

class Tick (α : Type u) where
  tick : α → α

-- merge x y = merge y x
class Merge (α : Type u) where
  merge : α → α → α

-- (x : σ) → (f : (σ → α)) → m α := return (f x)
class Stamp (m : Type u → Type v) (σ : Type s) (α : Type u) where
  stamp : σ → m α

class Delta (α : Type u) (δ : Type u) where
  delta : α → α → δ

----=============----
----= INSTANCES =----
----=============----

def rgt [BEq α] [Ord α] (x y : α) :=
  if Ord.compare x y == Ordering.gt then x else y

instance [OfNat α 1] [Add α] : Tick α where
  tick := (· + 1)

instance [Ord α] : Merge α where
  merge x y := if (Ord.compare x y == Ordering.gt) then x else y

-- TODO: Find a decent Vec n implementation and make an instance for it.
instance [BEq α] [Ord α] [BEq (List α)] [FP.Partial (List α)]
         : Merge ((List α) × FalsePositive) where
  merge xs2 ys2 :=
    match (xs2, ys2) with
    | ((xs, p₁), (ys, p₂)) =>
      match (FP.Partial.compare xs ys) with
      | .gt p₃ => (xs, p₁ * p₃)
      | .lt p₃ => (ys, p₂ * p₃)
      | .eq => (xs, p₁)
      | .incomparable =>
        let zipped :=
          List.zipWith rgt xs ys
        (zipped, p₁ * p₂)

end Straume.Clock
