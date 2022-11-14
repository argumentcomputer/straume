namespace Straume.Combinators

/-
"Anti" is a combinator that transforms binary functions into other binary functions.
It shall preserve the first argument iff the application of the function to another argument returns something else other than the first.
Otherwise, it shall make the resulting function return the second argument.
-/
def anti (f : α → α → α) [BEq α] : α → α → α :=
  fun x y =>
    let z := f x y
    if z == x then y else x

/-
Oh COME ON!
-/
def const : α → β → α
  | a, _ => a
