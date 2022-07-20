import Straume.Prob

/-
Exports Straume.Prob.Ordering.Comparable.FalsePositive.Partial typeclass.
Useful for bloom filters and clocks.
-/
namespace Straume.Prob.Ordering

namespace Comparable
inductive Comparison α where
| incomparable
| eq -- We use eq from BEq, so it's always certain
| lt : α → Comparison α
| gt : α → Comparison α

namespace FalsePositive
open Straume.Prob.FalsePositive

-- Straume.Prob.Ordering.Comparable.FalsePositive.Partial
class Partial (α : Type u) [BEq α] where
  lt : α → α → PSum Unit FalsePositive
  le : α → α → PSum Unit FalsePositive :=
    fun x y => match lt x y with
               | .inl _ => .inl ()
               | .inr z => .inr $ assure z (forSure $ BEq.beq x y)
  compare : α → α → Comparison FalsePositive :=
    fun x y => match le x y with
               | .inl _ => .incomparable
               | .inr .no => match le y x with
                             | .inl _ => .incomparable
                             | .inr .no => .eq
                             | .inr z => .gt z
               | .inr z => .lt z

end FalsePositive

/- TODO -/
namespace FalseNegative
end FalseNegative

end Comparable

/- TODO -/
namespace Incomparable
/- TODO -/
namespace FalsePositive
end FalsePositive
/- TODO -/
namespace FalseNegative
end FalseNegative
end Incomparable
