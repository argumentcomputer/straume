import Straume.Chunk
import Straume.Iterator
import Straume.Zeptoparsec
import Straume.MonadEmit

open Straume.Chunk (Chunk Terminable)
open Straume.Chunk
open Straume.Iterator (Iterable Iterator iter)
open Zeptoparsec
      renaming Parsec → Zepto.Parsec
open Zeptoparsec
      renaming ParseResult → Zepto.Res

/- This module is designed first and foremost to provide Megaparsec users a way to work with greater-than RAM and infinite streams.

TODO: SINK UP OTHER SIGNATURES WITH SIGNATURE FOR AKA
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

/- Very generic version of Chunky. Everything that's Chunky is also Avots.
TODO: Validate that Avots is using SLICES where Aka is using APPEND. -/
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

class Biterable (β : Type v) (α : outParam (Type u)) where
  composite : Type u
  atomic : Type v

instance : Biterable Char String where
  composite := String
  atomic := Char

class Flood (m : Type u → Type v)
            (s : Type u) where
  flood (_ctx : m s) (_buffer : Nat := 2048)
        : m s

/- Do we need this even?.. I guess, nice-to-have. -/
class Notch (v : Type u) where
  notch : v → Nat

/- Preventing typeclass clashes in transient dependencies in style. -/
class Coco (x : Type u) (y : outParam (Type u)) where
  coco : y → x
  replace : y → x → y

instance : Coco String (String × IO.FS.Handle) where
  coco := Prod.fst
  replace kl k := (k, Prod.snd kl)

open MonadEmit (MonadEmit) in
private def readStringNUnchecked (h : IO.FS.Handle) (n : Nat)
                                 : IO (String × IO.FS.Handle) := MonadEmit.askFrom h n

instance : Aka IO (String × IO.FS.Handle) Chunk Char where
  take1 mxh b := do
    let (x, h) ← mxh
    match x.data with
    | [] =>
        let (x₁, h₁) ← readStringNUnchecked h b
        match x₁.data with
        | []      => pure (Chunk.nil, ("", h₁))
        | y :: [] =>
            let isEof ← BaseIO.toIO $ IO.FS.Handle.isEof h₁
            if isEof then pure (Chunk.fin (y, Terminator.eos), ("", h₁))
            -- If b = 1, we want to continue, even though we just read 1 byte
            else pure (Chunk.cont y, ("", h₁))
        | y :: rest => pure (Chunk.cont y, (String.mk rest, h₁))
    | y :: [] =>
        let (x₁, h₁) ← readStringNUnchecked h b
        match x₁.data with
        | [] => pure (Chunk.fin (y, Terminator.eos), ("", h₁))
        | _otherwise => pure (Chunk.cont y, (x₁, h₁))
    | y :: rest => pure (Chunk.cont y, (String.mk rest, h))

instance : Flood IO (String × IO.FS.Handle) where
  flood mxh b := do
    let (x, h) ← mxh
    let (x₁, h₁) ← readStringNUnchecked h b
    pure (String.append x x₁, h₁)

def takeN {℘ ⅌ : Type u} (mx : m s) (n : Nat) (b := 2048)
          [Aka m s f β] [Coco ℘ s] [Flood m s] [Terminable f ℘] [Monad m] [Iterable ℘ ⅌] [Biterable ⅌ ℘]
          : m (f ℘ × s) := do
  -- BEST EFFORT STARTS
  let src ← mx
  let l := Iterable.length $ (Coco.coco src : ℘)
  let src₁ ← Flood.flood mx (max b ((n - l) + 1))
  let buffer₁ : ℘ := Coco.coco src₁
  let k := Iterable.length buffer₁
  -- BEST EFFORT ENDS
  -- EXTRACTION STARTS
  let it₀ : Iterator ℘ := iter buffer₁
  let it₁ := { it₀ with i := n }
  let y := Iterable.extract it₀ it₁
  -- TODO: MAKE SURE THAT ALL THE EXTRACTS IN Iterable INSTANCES HAVE THE SAME SEMANTICS!!!
  -- (RE: OFF BY ONE ERRORS)
  let restIt₀ := { it₀ with i := n }
  let restIt₁ := { it₀ with i := k }
  -- | v(0)    v(4)
  -- | с а ш к а в ы х о д и с м я ч о м |
  let rest := Iterable.extract restIt₀ restIt₁
  -- EXTRACTION ENDS
  -- CHUNK PREPARATION STARTS
  let res? := match k - n with
  | 1 => Terminable.mkCont y
  | _otherwise => Terminable.mkFin (y, .eos)
  let res := if (k == 0) && (l == 0) then Terminable.mkNil else res?
  -- CHUNK PREPARATION ENDS
  pure (res, Coco.replace src₁ rest)

-- #eval takeN
