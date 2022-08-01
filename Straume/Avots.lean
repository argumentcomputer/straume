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

/- This module is designed first and foremost to provide Megaparsec users a way to work with greater-than RAM and infinite streams.

-/
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
  -- TODO: PERHAPS MAKE A STRATEGY CONFIG FOR ATTEMPTS / GIVING UP
  take1 : m source → m ((Chunk TCompositeValue) × source)
  takeN (container : Type u → Type u)
        : Nat → m source → m (container (Chunk TCompositeValue) × source)
  listN := takeN List
  arrN := takeN Array
--   takeZepto
--       (_p : Zepto.Parsec TCompositeValue TCompositeValue)
--       : m source → m ((Chunk TCompositeValue) × source)
--   takeNZepto
--       (container : Type u → Type u)
--       (_n : Nat)
--       (_p : Zepto.Parsec TCompositeValue TCompositeValue)
--       : m source → m (container (Chunk TCompositeValue) × source)
--   listNZepto := takeNZepto List
--   arrNZepto := takeNZepto Array
  chunkLength (wr : m (Chunk TCompositeValue))
              : m (Chunk TCompositeValue × Nat) :=
      wr >>= fun c => pure (c, Iterable.length c)

--

/- Very generic version of Chunky. Everything that's Chunky is also Avots. -/
class Avots (m : Type u → Type v)
            (s : Type u)
            (v : Type u) where
  take1 : m s → m (v × s)
  takeN (t : Type u → Type u) : Nat → m s → m (t v × s)
  listN := takeN List
  arrN := takeN Array
--   parse (p : Type u → Type u → Type u)
--         : p v v → m s → m (v × s)
--   parseN (t : Type u → Type u) (p : Type u → Type u → Type u)
--          : Nat → p v v → m s → m (t v × s)
--   parseList := parseN List
--   parseArr := parseN Arr
  chunkLength : m v → m (Nat × v)

/- A way to read atomic values `v` out of a source `s`, which emits `Iterable α v`.
The information about finality is tacked onto the values of type `v` via type `f`.
An example of such `f` is `Chunk`. -/
class Aka (m : Type u → Type v)
          (s : Type u)
          (f : Type u → Type u)
          (v : Type u) where
          -- TODO: See if we can express that _buffer > 0 in types
  take1 (_source : m s) (_buffer : Nat := 2048)
        : m (f v × s)
  takeN (t : Type u → Type u) (_n : Nat) (_source : m s) (_buffer : Nat := 2048)
        : m (f (t v) × s)
  listN := takeN List
  arrN := takeN Array
--   parse (p : Type u → Type u → Type u)
--         : p v v → m s → m (v × s)
--   parseN (t : Type u → Type u) (p : Type u → Type u → Type u)
--          : Nat → p v v → m s → m (f (t v) × s)
--   parseList := parseN List
--   parseArr := parseN Arr
  chunkLength : m v → m (Nat × v)

private def readStringN (_ : IO.FS.Handle) (n : Nat) : IO (String × IO.FS.Handle) := sorry

instance : Aka IO (String × IO.FS.Handle) Chunk Char where
  take1 mxh b := do
    let (x, h) ← mxh
    match x.data with
    | [] =>
        let (x₁, h₁) ← readStringN h b
        match x₁.data with
        | []      => pure (Chunk.nil, ("", h₁))
        | y :: [] =>
            let isEof ← BaseIO.toIO $ IO.FS.Handle.isEof h₁
            if isEof then pure (Chunk.fin (y, Terminator.eos), ("", h₁))
            -- If b = 1, we want to continue, even though we just read 1 byte
            else pure (Chunk.cont y, ("", h₁))
        | y :: rest => pure (Chunk.cont y, (String.mk rest, h₁))
    | y :: [] =>
        let (x₁, h₁) ← readStringN h b
        match x₁.data with
        | [] => pure (Chunk.fin (y, Terminator.eos), ("", h₁))
        | _otherwise => pure (Chunk.cont y, (x₁, h₁))
    | y :: rest => pure (Chunk.cont y, (String.mk rest, h))
  takeN := sorry
  chunkLength := sorry

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
