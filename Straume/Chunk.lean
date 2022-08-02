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
deriving Repr

instance [ToString α] : ToString (Chunk α) where
  toString x := match x with
  | .nil => "Chunk.nil"
  | .cont y => s!"Chunk.cont \"{y}\""
  | .fin (y, t) => s!"Chunk.fin (\"{y}\", {t})"

export Chunk (nil cont fin)

class Terminable (f : Type u → Type u) (α : Type u) (ε : outParam (Type v)) where
  mkNil : f α
  mkCont : α → f α
  mkFin : α → f α
  mkFault : α → ε → f α
  un : f α → Option α
  reason : f α → Option Terminator

instance {α : Type u} : Terminable Chunk α IO.Error where
  mkNil := .nil
  mkCont := .cont
  -- TODO: Currently there's no way to chain reason into mkFin or Fault because we can't generically switch over ε.
  -- TODO: Move Failable away from Terimable... Solving :up: and making the typeclass working properly?..
  mkFin (x : α) := .fin (x, .eos)
  mkFault (x : α) (e : IO.Error) := .fin (x, .ioerr e)
  un (x : Chunk α) := match x with
  | .nil => .none
  | .cont res => .some res
  | .fin (res, _) => .some res
  reason (x : Chunk α) := match x with
  | .nil => .none
  | .cont _ => .none
  | .fin (_, e) => .some e

instance : Functor Chunk where
  map f fxs := match fxs with
    | .nil => .nil
    | .cont xs => .cont $ f xs
    | .fin (xs, terminator) => .fin (f xs, terminator)

instance : Inhabited (Chunk α) where
  default := .nil

private def coreturn' (fxs : Chunk α) [Inhabited α] : α :=
  match fxs with
    | .nil => default
    | .cont xs => xs
    | .fin (xs, _) => xs

variable (γ : Type u) [BEq γ] [Inhabited γ] [Iterable γ ⅌]

instance : Iterable (Chunk γ) ⅌ where
  push fxs y := (fun xs => Iterable.push xs y) <$> fxs
  length fxs := Iterable.length $ coreturn' fxs
  hasNext it := Iterable.hasNext $ Iterator.mk (coreturn' it.s) (it.i)
  next it :=
    Iterator.mk it.s (Iterable.next $ Iterator.mk (coreturn' it.s) (it.i)).i
  extract it₁ it₂ :=
    let g := Iterator.extract (Iterator.mk (coreturn' it₁.s) (it₁.i))
                              (Iterator.mk (coreturn' it₂.s) (it₂.i))
    -- TODO: is this correct?
    if g == default then
      .nil
    else
      (const g) <$> it₁.s
  curr it := Iterator.curr (Iterator.mk (coreturn' it.s) (it.i))
