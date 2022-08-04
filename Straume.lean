import Straume.Aka
import Straume.Buffer
import Straume.Chunk
import Straume.Clock
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
/- Stream with an injective type family from composite `v` to atomic `a`. -/
class Straume (m : Type u → Type v)
              (s : Type u)
              (f : Type u → Type u)
              (v : Type u)
              (a : outParam (Type u))
              [outParam (Terminable f)]
              [outParam (Iterable v a)] where
  take1 (_source : s) (_bufferSize : Nat) : m ((f a) × s)
  takeN (_readQty : Nat) (_source : s) (_bufferSize : Nat) : m ((f v) × s)
  takeWhile (_atomicMatcher : a → Bool) (_source : s) (_bufferSize : Nat) : m ((f v) × s)
  chunkLength (chunk : f v) : Nat := Aka.chunkLength chunk
