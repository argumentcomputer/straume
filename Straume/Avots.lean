import Straume.Chunk
import Straume.Iterator

open Straume.Chunk (Chunk)
open Straume.Iterator (Iterable)

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
class Avots (m : Type u → Type v)
            (source : Type u)
            (TCompositeValue : Type u)
            [Iterable TCompositeValue β] where
  take1 : m source → m (Chunk TCompositeValue × source)
  takeN (container : Type u → Type u)
        : Nat → m source → m (container (Chunk TCompositeValue) × source)
  -- takeZepto :

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
