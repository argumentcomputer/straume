import Straume.Chunk
import Straume.Iterator
import Straume.Zeptoparsec
import Straume.MonadEmit

open Straume.Chunk (Chunk Terminable)
open Straume.Chunk
open Straume.Iterator (Iterable Iterator iter)
open Straume.Iterator
      renaming Bijection → It.Bijection
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

-- open Straume.Combinators in
-- def take1 {f : Type u → Type u} {α β : Type u}
--           (mx : m s) (b := 2048)
--           [Coco α s] [Flood m s] [Terminable f β] [Monad m] [Iterable α β] [It.Bijection β α]
--           : m ((f β) × s) := do
--   let src₀ ← mx
--   let buff₀ : α := Coco.coco src₀
--   let srcₑ ← Flood.flood mx $ max b (1 + 1)
--   let buffₑ : α := Coco.coco srcₑ
--   let mkFB : β → f β :=
--     if Iterable.length buffₑ > 1 then
--       Terminable.mkCont
--       -- pure (Terminable.mkCont $ Iterable.curr (iter buff₀), srcₑ)
--     else if Iterable.length buffₑ == 1 then
--       -- pure (Terminable.mkFin $ Iterable.curr (iter buff₀), srcₑ)
--       Terminable.mkFin
--     else
--       -- pure (Terminable.mkNil, srcₑ)
--       const Terminable.mkNil
--   pure (mkFB $ Iterable.curr (iter buff₀), Iterable.srcₑ)

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

def take1 {f : Type u → Type u} {α β : Type u}
          (mx : m s) (b := 2048)
          [Coco α s] [Flood m s] [Terminable f] [Monad m] [Iterable α β] [It.Bijection β α]
          : m ((f β) × s) := do
  let ((y, s₁) : (f α × s)) ← takeN mx 1 b
  let fit := iter <$> y
  let res := Iterable.curr <$> fit
  pure (res, s₁)
  -- takeN mx 1 b >>= fun (y, s₁) => pure ((Iterable.curr ∘ iter ∘ Coco.coco) <$> y, s₁)

---------------
-- takeWhile --
---------------

private partial def takeWhileDo
    {f : Type u → Type u} {α β : Type u}
    (φ : β → Bool) (mx : m s) (b : Nat) (acc : f α)
    [Coco α s] [Iterable α β] [Terminable f]
    [Monad m] [Inhabited (m (f α × s))] [Inhabited α] [Flood m s] [It.Bijection β α] -- [ToString α] [ToString β]
    : m (f α × s) := do
  let stream₀ ← mx
  let ((atom, stream) : (f β × s)) ← take1 mx b
  match Terminable.un atom with
  | .none => pure (acc, stream₀)
  | .some c =>
    if φ c then
      match (Terminable.un acc, Terminable.reason acc, Terminable.reason atom) with
      -- cont cases.
      | (.none, .none, .none) => takeWhileDo φ (pure stream) b $ Terminable.mkCont (Iterable.push default c)
      | (.some ys, .none, .none) => takeWhileDo φ (pure stream) b $ Terminable.mkCont (Iterable.push ys c)
      -- fin cases.
      | (.none, .none, .some ()) =>
        pure (Terminable.mkFin $ Iterable.push default c, stream)
      | (.some ys, .none, .some ()) =>
        pure (Terminable.mkFin $ Iterable.push ys c, stream)
      -- nil case.
      | _otherwise => pure (acc, stream₀)
    else
      pure (acc, stream₀)

partial def takeWhile (φ : β → Bool) (mx : m s) (b : Nat := 2048)
  [Coco α s] [Iterable α β] [Terminable f]
  [Monad m] [Inhabited (m (f α × s))] [Inhabited α] [It.Bijection β α] [Flood m s]
    : m (f α × s) := takeWhileDo φ mx b (Terminable.mkNil : f α)

-----------------
-- chunkLength --
-----------------

def chunkLength (fx : f α) [Terminable f] [Iterable α β] : Nat :=
  match (Terminable.un fx) with
  | .none => 0
  | .some e => Iterable.length e

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
  take1 mx b := take1 mx b
