import Straume.Zeptoparsec
import Straume.Iterator
import Straume.Combinators

open Straume.Iterator (Iterable Iterator)
open Straume.Combinators (const)

/- Chunks bundle Stream data into objects. The benchmark for the good UX for
those is for them to be parsable entirely with a Megaparsec. -/
namespace Straume.Chunk
universe u


/-
A way to terminate a stream.
`eos` means "end of stream", expected one.
`timeout` means that the Lean runner itself timed out (note that ioerr has `timeExpired` constructor, which is the same, but for OS timeouts)
`ioerr` means that we were running the stream as an IO task, and we got an IO error while performing it.

TODO: do we want to let the user control max chunk size and error out if it's too big?
-/
inductive Terminator where
  | eos
  | timeout
  | ioerr : IO.Error → Terminator

instance : ToString Terminator where
  toString x := match x with
  | .eos => "Terminator.eos"
  | .timeout => "Terminator.timeout"
  | .ioerr _e => "Terminator.⟪system error⟫"

instance : Repr Terminator where
  reprPrec x _n := ToString.toString x

/-
Suppose we have a variable length binary protocol such that the message length
is encoded as a three bit integer.

 |-3-|----n----|-3-|---|
 | 7 | 1001111 | 1 | 0 |

Naturally, chunks are:
 .cont [1,0,0,1,1,1,1],
 .fin ( [0,0,1], .eos )

and are of type `Chunk Bit (List Bit)`.

But if we insist, we consume it bit by bit by typing it as `Chunk Bit Bit`:
 | 111 1001111 011 001 |
Chunks are
 .cont 1
 .cont 1
 .cont 1
 .cont 1
 .cont 0
 ...
 .fin ( 1, .eos )

I hope it's clear. 🙇
-/
inductive Chunk (α : Type u) where
  | nil
  | cont : α → Chunk α
  | fin : α × Terminator → Chunk α
  deriving Inhabited, Repr

export Chunk (nil cont fin)

instance [ToString α] : ToString (Chunk α) where
  toString
    | .nil => "Chunk.nil"
    | .cont y => s!"Chunk.cont \"{y}\""
    | .fin (y, t) => s!"Chunk.fin (\"{y}\", {t})"

instance : Functor Chunk where
  map | _, .nil => .nil
      | f, .cont xs => .cont $ f xs
      | f, .fin (xs, terminator) => .fin (f xs, terminator)

instance : Inhabited (Chunk α) where
  default := .nil

-------------------------------
----       Terminable      ----
-------------------------------

-- `Terminable` only works with `.eos`, which we "model" with `Option Unit`
-- `Terminable` models info about finality tacked onto values.
class Terminable (f : Type u → Type u) where
  mkNil : f α
  mkCont : α → f α
  mkFin : α → f α
  un : f α → Option α
  reason : f α → Option Unit

instance : Terminable Chunk where
  mkNil := .nil
  mkCont := .cont
  mkFin x := .fin (x, .eos)
  un | .nil => .none
     | .cont res => .some res
     | .fin (res, _) => .some res
  reason
    | .nil => .none
    | .cont _ => .none
    | .fin _ => .some ()

export Terminable (mkNil mkCont mkFin)

def coreturn [Inhabited α] [Terminable f] (fxs : f α) : α :=
  (Terminable.un fxs).getD default

instance [Terminable f] : Inhabited (f α) where
  default := mkNil

instance [Terminable f] : Functor f where
  map φ fa :=
    match (Terminable.un fa, Terminable.reason fa) with
    | (.some y, .none) => mkCont $ φ y
    | (.some y, .some ()) => mkFin $ φ y
    | _otherwise => mkNil

instance [Iterable α β] [Terminable f] [Inhabited α] [BEq α]
    : Iterable (f α) β where
  push fxs y := (fun xs => Iterable.push xs y) <$> fxs
  length fxs := Iterable.length $ coreturn fxs
  hasNext it := Iterable.hasNext {it with s := coreturn it.s}
  next it :=
    let itᵢ := Iterable.next {it with s := coreturn it.s}
    { it with i := itᵢ.i }
  extract it₁ it₂ :=
    let g := Iterable.extract {it₁ with s := coreturn it₁.s}
                              {it₂ with s := coreturn it₂.s}
    -- TODO: is this correct?
     if g == default then mkNil else (const g) <$> it₁.s
  curr it := Iterable.curr {it with s := coreturn it.s}
