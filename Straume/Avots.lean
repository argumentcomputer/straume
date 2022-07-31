import Straume.Chunk
import Straume.Iterator
import Straume.Zeptoparsec

open Straume.Chunk (Chunk)
open Straume.Chunk
open Straume.Iterator (Iterable)
open Zeptoparsec
      renaming Parsec → Zepto.Parsec
open Zeptoparsec
      renaming ParseResult → Zepto.Res

namespace Straume.Avots

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


/- Gets one or more finite (for the time being) `Chunk`s out of a perhaps infinite stream.
These chunks themselves are composite.
As in, their underlying data type contains stuff.
I'm sorry for using C++ notation to denote the composite value type.
I promise, I tried to come up with a juicy, semantic, one-letter name for it, but failed.
-/
class Chunky (m : Type u → Type v)
             (source : Type u)
             (TCompositeValue : Type u)
             [BEq TCompositeValue] [Inhabited TCompositeValue] [Iterable TCompositeValue β]
             [Monad m]
             where
  take1 : m source → m ((Chunk TCompositeValue) × source)
  takeN (container : Type u → Type u)
        : Nat → m source → m (container (Chunk TCompositeValue) × source)
  listN := takeN List
  arrN := takeN Array
  takeZepto
      (_p : Zepto.Parsec TCompositeValue TCompositeValue)
      : m source → m ((Chunk TCompositeValue) × source)
  takeNZepto
      (container : Type u → Type u)
      (_n : Nat)
      (_p : Zepto.Parsec TCompositeValue TCompositeValue)
      : m source → m (container (Chunk TCompositeValue) × source)
  listNZepto := takeNZepto List
  arrNZepto := takeNZepto Array
  chunkLength (wr : m (Chunk TCompositeValue))
              : m (Chunk TCompositeValue × Nat) :=
      wr >>= fun c => pure (c, Iterable.length c)


/- Very generic version of Chunky. Everything that's Chunky is also Avots. -/
class Avots (m : Type u → Type v)
            (s : Type u)
            (v : Type u)
            (p : Type u → Type u → Type u) where
  take1 : m s → m (v × s)
  takeN (t : Type u → Type u) : Nat → m s → m (t v × s)
  listN := takeN List
  arrN := takeN Array
  parse : p v v → m s → m (v × s)
  parseN (t : Type u → Type u) : Nat → p v v → m s → m (t v × s)
  parseList := parseN List
  parseArr := parseN Arr
  chunkLength : m v → m (Nat × v)

-- structure Greater (α : Type) where
--   (β : Type)
--   y : (α × β)

-- structure Same (α : Type) where
--   id : α

-- #check Same Int
-- #check Int

-- #check Int
-- #check Greater Int

-- class Avv ... where
--   take1 : m a → m (f b × a)
--   takeN (φ : ...) : Nat → m a → m (φ (f b) × a)
--   ...
