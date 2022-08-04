import Straume.Chunk
import Straume.Coco
import Straume.Flood
import Straume.Iterator
import Straume.Zeptoparsec

open Straume.Chunk (Chunk Terminable)
open Straume.Coco (Coco)
open Straume.Flood (Flood)
open Straume.Iterator (Iterable iter)
open Zeptoparsec renaming Parsec → Zepto.Parsec
open Zeptoparsec renaming ParseResult → Zepto.Res


/-
  This module is designed first and foremost to provide Megaparsec users
  with a way to work with greater-than-RAM and infinite streams.
-/
namespace Straume.Aka

universe u
universe v

-- class Stream (S : Type) where
--   Token : Type
--   ordToken : Ord Token
--   Chunk \a : Type
--   ordChunk \a : Ord Chunk \a
--   tokenToChunk : Token → Chunk \a
--   tokensToChunk : List Token → Chunk \a
--   chunkToChunk \a : Chunk \a → List Token
--   chunkLength : Chunk \a → Nat
--   take1 : S → Option (Token × S)
--   takeN : Nat → S → Option (Chunk \a × S)
--   takeWhile : (Token → Bool) → S → (Chunk \a × S)

-------------------------------
----         takeN         ----
-------------------------------

def takeN {f : Type u → Type u} {α β : Type u}
          (mx : m s) (n : Nat) (b : Nat := 2048)
          [Coco α s] [Flood m s] [Terminable f] [Monad m] [Iterable α β]
          : m (f α × s) := do
  -- BEST EFFORT
  let src ← mx
  let l := Iterable.length (Coco.coco src : α)
  let srcₑ ← Flood.flood mx $ max b ((n - l) + 1) -- We expand the buffer
  -- EXTRACTION
  let it₀ := iter $ Coco.coco srcₑ
  let it₁ := { it₀ with i := n }
  let firstN := Iterable.extract it₀ it₁
  -- CHUNK PREPARATION
  let k := Iterable.length $ it₀.s
  let res :=
    if k == 0 && l == 0
    then Terminable.mkNil -- Expansion unsuccessful => Stream was always empty
    else match k - n with
      | 0 => Terminable.mkFin firstN -- We expanded to less than `n`
      | _otherwise => Terminable.mkCont firstN
  pure (res, Coco.replace srcₑ $ Iterable.extract it₁ { it₁ with i := k })

-------------------------------
----      chunkLength      ----
-------------------------------

def chunkLength (fx : f α) [Terminable f] [Iterable α β] : Nat :=
  match (Terminable.un fx) with
  | .none => 0
  | .some e => Iterable.length e

-------------------------------
----       Aka class       ----
-------------------------------

/-
  A way to read atomic values `v` out of a source `s`,
  which emits `Iterable α v`.
  The information about finality is tacked onto the values of type `v`
  via type `f`.
  An example of such `f` is `Chunk`.
-/
class Aka (m : Type u → Type v)
          (s : Type u)
          (f : Type u → Type u)
          (v : Type u) where
                        -- TODO: Can we express _buffer > 0 in types?
  take1 (_source : m s) (_buffer : Nat := 2048) : m ((f v) × s)
