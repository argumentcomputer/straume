namespace Straume.Prob.Ordering

structure Incomparable

inductive Comparison α where
| incomparable
| eq -- We use eq from BEq, so it's always certain
| lt : α → Comparison α
| gt : α → Comparison α