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

open Straume.Iterator in
open Straume.Chunk in
open Straume.Aka in
open Straume.Flood in
open Straume.Coco in
/- Stream with an injective type family from composite `v` to atomic `a`. -/
class Straume (m : Type u → Type v)
              (s : Type u)
              (f : Type u → Type u)
              (v : Type u)
              (a : outParam (Type u))
              [Terminable f]
              [Flood m s]
              [Monad m]
              [Coco v s]
              [Inhabited α]
              [outParam (Iterable v a)] where
  take1 (_source : s) (_bufferSize : Nat) : m (f a × s) :=
    Aka.take1 _source _bufferSize
  takeN (_readQty : Nat) (_source : s) (_bufferSize : Nat) : m (f v × s) :=
    Aka.takeN _source _readQty _bufferSize
  takeWhile (_atomicMatcher : a → Bool) (_source : s) (_bufferSize : Nat) : m (f v × s) := Aka.takeWhile _atomicMatcher _source _bufferSize
  chunkLength (chunk : f v) : Nat := Aka.chunkLength chunk

open Straume.Combinators
#check λs => Straume.Aka.takeWhile (const true) s 2048
