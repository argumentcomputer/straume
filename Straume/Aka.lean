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
  take1 (_source : m s) (_buffer : Nat := 2048)
        : m ((f v) × s)

/- A way to flood a buffer of some source `s` with more data. -/
class Flood (m : Type u → Type v)
            (s : Type u) where
  flood (_ctx : m s) (_buffer : Nat := 2048)
        : m s

/- Discretely-measurable stuff. -/
class Notch (v : Type u) where
  notch : v → Nat

/- `Coco`s are `y`s that cary and allow to swap out `x`s.
So `x`s are "contained" in `y`s.
Sort of Flipped Coe with an additional `replace` method.
Preventing typeclass clashes in transient dependencies in style. -/
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
        | y :: rest =>
          pure (Chunk.cont y, (String.mk rest, h₁))
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

def takeN {f : Type u → Type u} {℘ ⅌ : Type u} (mx : m s) (n : Nat) (b := 2048)
          [Coco ℘ s] [Flood m s] [Terminable f ℘ ε] [Monad m] [Iterable ℘ ⅌]
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
  | 0 => Terminable.mkFin y
  | _otherwise => Terminable.mkCont y
  let res := if (k == 0) && (l == 0) then Terminable.mkNil else res?
  -- CHUNK PREPARATION ENDS
  pure (res, Coco.replace src₁ rest)

private partial def takeWhileDo {f : Type u → Type u} {℘ ⅌ : Type u}
                                (φ : ⅌ → Bool) (mx : m s) (b : Nat) (acc : f ℘)
                                [Coco ℘ s] [Iterable ℘ ⅌] [Terminable f ℘ ε] [Terminable f ⅌ ε] [Aka m s f ⅌] [Monad m] [Inhabited (m (f ℘ × s))] [Inhabited ℘]
                                : m (f ℘ × s) := do
  let stream₀ ← mx
  let (atom, stream) ← (Aka.take1 mx b : m (f ⅌ × s))
  match Terminable.un atom with
  | .none => pure (acc, stream₀)
  | .some c =>
    if φ c then
      match (Terminable.un acc, Terminable.reason acc, Terminable.reason atom) with
      -- cont cases.
      | (.none, .none, .none) => takeWhileDo φ (pure stream) b $ Terminable.mkCont (Iterable.push default c)
      | (.some ys, .none, .none) => takeWhileDo φ (pure stream) b $ Terminable.mkCont (Iterable.push ys c)
      -- fin cases. We forget the error. It's a TODO.
      | (.none, .none, .some _e) => pure (Terminable.mkFin (Iterable.push default c), stream)
      | (.some ys, .none, .some _e) => pure (Terminable.mkFin (Iterable.push ys c), stream)
      -- nil case.
      | _otherwise => pure (acc, stream₀)
    else
      pure (acc, stream₀)

partial def takeWhile {f : Type u → Type u} {℘ ⅌ : Type u} (φ : ⅌ → Bool) (mx : m s) (b := 2048)
              [Coco ℘ s] [Iterable ℘ ⅌] [Terminable f ℘ ε] [Terminable f ⅌ ε] [Aka m s f ⅌] [Monad m] [Inhabited (m (f ℘ × s))] [Inhabited ℘]
              : m (f ℘ × s) :=
  takeWhileDo φ mx b (Terminable.mkNil : f ℘)

def chunkLength {f : Type u → Type u} {℘ ⅌ : Type u}
                (fx : f ℘)
                [Terminable f ℘ ε] [Iterable ℘ ⅌]
                : Nat :=
  match (Terminable.un fx) with
  | .none => 0
  | .some e => Iterable.length e
