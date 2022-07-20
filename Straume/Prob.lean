import Straume.Combinators

namespace Straume.Prob

/- False positives are used to represent probabilistic results.

TODO: It's known that the runtime we're targetting at Yatima isn't well-suited for Floats.
Our ProbParOrd wants Float probabilities.
Perhaps, it makes sense, for probabilistic computations, to equip those with a probability approximation facilities to convert Floats to some close rational numbers.
Write class ToRational or find Rational.ofFloat?..
-/
inductive FalsePositive where
| perhaps : Float → FalsePositive
| no
  deriving Repr, BEq

/- False negatives aren't currently used and are defined just for symmetry. -/
inductive FalseNegative where
| yes
| hardly : Float → FalseNegative
  deriving Repr, BEq

---------------------------------------------

namespace FalsePositive

/-
FalsePositive absolute "true".
You can supply false as an argument to get a certain ".no".
-/
def forSure (x : Bool := true) : FalsePositive :=
  if x then .perhaps 1.0 else .no

/- Fuzzy "or", keeping the false positive with higher confidence. -/
def assure (x : FalsePositive) (y : FalsePositive) : FalsePositive :=
  match (x, y) with
  | (.perhaps _, .no) => x
  | (.perhaps xₙ, .perhaps yₙ) => if (xₙ > yₙ) then x else y
  | (_, _) => y

def doubt := Straume.Combinators.anti assure

inductive Comparison α where
| incomparable
| eq -- We use eq from BEq, so it's always certain
| lt : α → Comparison α
| gt : α → Comparison α

-- abbrev Incomparable := Unit

end FalsePositive

---------------------------------------------

namespace FalseNegative

/-
FalseNegative absolute "false".
You can supply "true" as its argument to get a certain "yes".
-/
def surelyNot (x : Bool := true) : FalseNegative :=
  if x then .hardly 1.0 else .yes

/- Kind of like and, keeping the false negative with higher confidence. -/
def disprove (x : FalseNegative) (y : FalseNegative) : FalseNegative :=
  match (x, y) with
  | (.hardly _, .yes) => x
  | (.hardly xₙ, .hardly yₙ) => if (xₙ > yₙ) then x else y
  | (_, _) => y

/- Kind of like or, keeping the false positive with the highest confidence. -/
def convince := Straume.Combinators.anti disprove

inductive Comparison α where
| incomparable : α → Comparison α
| eq -- We use eq from BEq, so it's always certain
| lt
| gt

-- structure Relation := Bool

end FalseNegative

end Straume.Prob
