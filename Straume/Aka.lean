import Straume.Chunk
import Straume.Coco
import Straume.Flood
import Straume.Iterator

/-!
## The Aka class
This module is designed first and foremost to provide Megaparsec users
with a way to work with greater-than-RAM and infinite streams.
-/

open Straume (Chunk Terminable coreturn)
open Straume.Flood (Flood)
open Straume.Iterator (Iterable iter Bijection)

universe u v

-------------------------------
----       Aka class       ----
-------------------------------

/--
A way to read atomic values `v` out of a source `s`,
which emits `Iterable α v`.
The information about finality is tacked onto the values of type `v`
via type `f`.
An example of such `f` is `Chunk`.
-/
class Straume.Aka (m : Type u → Type v)
          (s : Type u)
          (f : Type u → Type u)
          (v : Type u) where
                        -- TODO: Can we express _buffer > 0 in types?
  take1 (_source : s) (_buffer : Nat := 2048) : m ((f v) × s)

section aka_instance

namespace Straume.Aka

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
-- TODO: ^^^^^^^^^ Keep this?

-------------------------------
----         takeN         ----
-------------------------------

variable {f : Type u → Type u} {α β s : Type u} {m : Type u → Type v} (src : s) 
         [Coco α s] [Flood m s] [Terminable f] [Monad m] [Iterable α β]

def takeN (n : Nat) (b : Nat := 2048) : m (f α × s) := do
  -- BEST EFFORT
  let l := Iterable.length (Coco.coco src : α)
  let srcₑ ← Flood.flood src $ max b ((n - l) + 1) -- We expand the buffer
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
----         take1         ----
-------------------------------

instance : Aka m s f β where
  -- We use `takeN` to snip off `α` of length 1 and then use
  -- `Iterable` to take the first (and only) element.
  take1 src b := takeN src 1 b >>= 
    fun ((y : f α), s₁) =>
    pure ((Iterable.curr ∘ iter) <$> y, s₁)

example : Aka IO (String × IO.FS.Handle) Chunk Char := by infer_instance
/-^^^^^^^^^^^^^^^^^
works, for example
TODO: Delete this comment
-/

end Straume.Aka

end aka_instance

-------------------------------
----       takeWhile       ----
-------------------------------

section aka_takeWhile

namespace Straume.Aka
  
variable {f : Type u → Type u} {α β s : Type u} (φ : β → Bool) 
         [Coco α s] [Iterable α β] [Terminable f] [Monad m] [Inhabited α] [Flood m s]

private partial def takeWhileDo (stream₀ : s) (b : Nat) (acc : f α) [Inhabited (m (f α × s))] 
    : m (f α × s) := do
  let ((atom : f β), stream) ← Aka.take1 stream₀ b
  match Terminable.un atom with
  | .none => pure (acc, stream₀)
  | .some c =>
    if φ c then
      match (Terminable.reason acc, Terminable.reason atom) with
      -- cont cases
      | (.none, .none) =>
        takeWhileDo stream b $
          Terminable.mkCont $ Iterable.push (coreturn acc) c
      -- fin cases
      | (.none, .some ()) =>
        pure (Terminable.mkFin $ coreturn acc, stream)
      -- nil case
      | _otherwise => pure (acc, stream₀)
    else
      pure (acc, stream₀)

partial def takeWhile (src : s) (b : Nat := 2048) [Inhabited (m (f α × s))] : m (f α × s) :=
  takeWhileDo φ src b Terminable.mkNil
 
end Straume.Aka

end aka_takeWhile
-------------------------------
----      chunkLength      ----
-------------------------------

section aka_length

namespace Straume.Aka

variable (fx : f α) [Terminable f] [Iterable α β]

def chunkLength : Nat :=
  match (Terminable.un fx) with
  | .none => 0
  | .some e => Iterable.length e

def storeLength : f Nat :=
  Iterable.length <$> fx

end Straume.Aka

end aka_length