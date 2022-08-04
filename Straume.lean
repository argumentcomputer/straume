import Straume.Aka
import Straume.Buffer
import Straume.Chunk
import Straume.Clock
import Straume.Coco
import Straume.Flood
import Straume.Iterator
import Straume.MonadEmit
import Straume.Pos
import Straume.Prob.Ordering
import Straume.Uni
import Straume.Zeptoparsec

namespace Straume

universe u
universe v

open Straume.Iterator
open Straume.Chunk
open Straume.Aka
open Straume.Flood
open Straume.Coco

/- The most generic stream!
You should depend on this to reap the benefits of people smarter than the authors of this library coming up with stream implementations!

One might wonder: "where is chunkLength?!".
This class is very generic and if you want to provide facilities to compute length of a chunk, instantiate it with v = (c × Nat)!
Incidentally, not limiting v to be a finite object, we achieve a degree of composability of infinite streams 🙈.
-/
class Straume (m : Type u → Type v)
              (s : Type u)
              (f : Type u → Type u)
              (v : Type u)
              {a : outParam (Type u)} where
  take1 (source : s) (bufferSize := 2048)
        : m (f a × s)
  takeN (readQty : Nat) (source : s) (bufferSize := 2048)
        : m (f v × s)
  takeWhile (matchAtomPredicate : a → Bool) (source : s) (bufferSize := 2048)
            : m (f v × s)

/- Stream with an bijective type family from composite `v` to atomic `a`.

One might wonder again: "where is chunkLength?!".
Since we use Straume as a convenience wrapper around Aka, and we **require `Iterable v a`**, you can always get the length of stuff stored under `f` by computing `Iterable.length`!
-/
instance
  {m : Type u → Type v}
  {s : Type u}
  {f : Type u → Type u}
  {v : Type u}
  {a : Type u}
  [Terminable f]
  [Flood m s]
  [Monad m]
  [Coco v s]
  [Inhabited (m (f v × s))]
  [Inhabited v]
  [Iterable v a]
  : @Straume m s f v a where
  take1 (source : s) (bufferSize := 2048) := Aka.take1 source bufferSize
  takeN readQty source (bufferSize := 2048) := Aka.takeN readQty source bufferSize
  takeWhile p source (bufferSize := 2048) := Aka.takeWhile p source bufferSize

export Straume (take1 takeN takeWhile)

-- open Straume.Combinators
-- #check λs => Straume.Aka.takeWhile (const true) s 2048
