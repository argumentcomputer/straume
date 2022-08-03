import Straume.Chunk
import Straume.Iterator
import Straume.Zeptoparsec
import Straume.MonadEmit

open Straume.Chunk (Chunk Terminable)
open Straume.Chunk
open Straume.Iterator (Iterable Iterator iter)
open Straume.MonadEmit (readStringNUnchecked)
open Zeptoparsec
      renaming Parsec → Zepto.Parsec
open Zeptoparsec
      renaming ParseResult → Zepto.Res

/- This module is designed first and foremost to provide Megaparsec users a way to work with greater-than RAM and infinite streams.
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

/- A way to read atomic values `v` out of a source `s`, which emits `Iterable α v`.
The information about finality is tacked onto the values of type `v` via type `f`.
An example of such `f` is `Chunk`. -/
class Aka (m : Type u → Type v)
          (s : Type u)
          (f : Type u → Type u)
          (v : Type u) where
          -- TODO: See if we can express that _buffer > 0 in types
  take1 (_source : m s) (_buffer : Nat := 2048) : m ((f v) × s)

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
        | y :: rest => pure (Chunk.cont y, (⟨rest⟩, h₁))
    | y :: [] =>
        let (x₁, h₁) ← readStringNUnchecked h b
        match x₁.data with
        | [] => pure (Chunk.fin (y, Terminator.eos), ("", h₁))
        | _otherwise => pure (Chunk.cont y, (x₁, h₁))
    | y :: rest => pure (Chunk.cont y, (⟨rest⟩, h))

/- A way to flood a buffer of some source `s` with more data. -/
class Flood (m : Type u → Type v)
            (s : Type u) where
  flood (_ctx : m s) (_buffer : Nat := 2048)
        : m s

instance : Flood IO (String × IO.FS.Handle) where
  flood mxh b := do
    let (x, h) ← mxh
    let (x₁, h₁) ← readStringNUnchecked h b
    pure (String.append x x₁, h₁)

/- Discretely-measurable stuff. -/
class Notch (v : Type u) where
  notch : v → Nat

/- `Coco`s are `y`s that carry and allow to swap out `x`s.
So `x`s are "contained" in `y`s.
Sort of Flipped Coe with an additional `replace` method.
Preventing typeclass clashes in transient dependencies in style. -/
class Coco (x : Type u) (y : outParam (Type u)) where
  coco : y → x
  replace : y → x → y

instance : Coco String (String × IO.FS.Handle) where
  coco := Prod.fst
  replace kl k := (k, Prod.snd kl)

def takeN (mx : m s) (n : Nat) (b : Nat := 2048)
          [Coco α s] [Flood m s] [Terminable f α ε] [Monad m] [Iterable α β]
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

---------------
-- takeWhile --
---------------

private partial def takeWhileDo
  {α β : Type u} (φ : β → Bool) (mx : m s) (b : Nat) (acc : f α)
    [Coco α s] [Iterable α β] [Terminable f α ε] [Terminable f β ε]
    [Aka m s f β] [Monad m] [Inhabited (m (f α × s))] [Inhabited α]
      : m (f α × s) := do
  let stream₀ ← mx
  let (atom, stream) ← (Aka.take1 mx b : m (f β × s))
  match Terminable.un atom with
  | .none => pure (acc, stream₀)
  | .some c =>
    if φ c then
      match (Terminable.un acc, Terminable.reason acc, Terminable.reason atom) with
      -- cont cases.
      | (.none, .none, .none) => takeWhileDo φ (pure stream) b $ Terminable.mkCont (Iterable.push default c)
      | (.some ys, .none, .none) => takeWhileDo φ (pure stream) b $ Terminable.mkCont (Iterable.push ys c)
      -- fin cases. We forget the error. It's a TODO.
      | (.none, .none, .some _e) =>
        pure (Terminable.mkFin $ Iterable.push default c, stream)
      | (.some ys, .none, .some _e) =>
        pure (Terminable.mkFin $ Iterable.push ys c, stream)
      -- nil case.
      | _otherwise => pure (acc, stream₀)
    else
      pure (acc, stream₀)

partial def takeWhile (φ : β → Bool) (mx : m s) (b : Nat := 2048)
  [Coco α s] [Iterable α β] [Terminable f α ε] [Terminable f β ε] [Aka m s f β]
  [Monad m] [Inhabited (m (f α × s))] [Inhabited α]
    : m (f α × s) := takeWhileDo φ mx b (Terminable.mkNil : f α)

-----------------
-- chunkLength --
-----------------

def chunkLength (fx : f α) [Terminable f α ε] [Iterable α β] : Nat :=
  match (Terminable.un fx) with
  | .none => 0
  | .some e => Iterable.length e
