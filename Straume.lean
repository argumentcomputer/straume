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

/- Stream with an bijective type family from composite `v` to atomic `a`. -/
class Straume (m : Type u → Type v)
              (s : Type u)
              (f : Type u → Type u)
              (v : Type u)
              [Terminable f]
              [Flood m s]
              [Monad m]
              [Coco v s]
              [Inhabited (m (f v × s))]
              [Inhabited v]
              [Iterable v a] where
  take1 (source : s) (bufferSize := 2048) : m (f a × s) :=
    Aka.take1 source bufferSize
  takeN (readQty : Nat) (source : s) (bufferSize := 2048) : m (f v × s) :=
    Aka.takeN readQty source bufferSize
  takeWhile (atomicMatcher : a → Bool) (source : s) (bufferSize := 2048) : m (f v × s) :=
    Aka.takeWhile atomicMatcher source bufferSize
  chunkLength (chunk : f v) : Nat := Aka.chunkLength chunk

export Straume (take1 takeN takeWhile chunkLength)

open Straume.Combinators
#check λs => Straume.Aka.takeWhile (const true) s 2048

instance : Straume IO (String × IO.FS.Handle) Chunk String := {}
