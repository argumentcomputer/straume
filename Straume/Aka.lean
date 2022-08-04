import Straume.Chunk
import Straume.Iterator
import Straume.Zeptoparsec

open Straume.Chunk (Chunk Terminable)
open Straume.Iterator (Iterable)
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
