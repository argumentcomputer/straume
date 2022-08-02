import Straume.Zeptoparsec
import Straume.Chunk
import Straume.Buffer
import Straume.Clock
import Straume.Uni
import Straume.Clock
import Straume.Prob.Ordering
import Straume.Pos
import Straume.MonadEmit

namespace Straume

universe u

class AB (a : Type u) (b : outParam (Type u)) where
  a2b : a → b

class BiAB (b : Type u) (a : outParam (Type u)) where
  getA : Type u
  getB : Type v

instance : AB String Char where
  a2b x := String.get x (String.Pos.mk 0)

instance : BiAB Char String where
  getA := String
  getB := Char

class Cont (f : Type u → Type u) (α : Type u) where
  mkNil : f α
  mkCont : α → f α
  mkFin : α → f α

inductive Chunk' (α : Type u) where
| nil
| cont : α → Chunk' α
| fin : α → Chunk' α

instance {α : Type u} : Cont Chunk' α where
  mkNil := .nil
  mkCont := .cont
  mkFin := .fin

class BEmit (s : Type u) (f : Type u → Type u) (b : Type u) where
  take1 : s → ((f b) × s)

abbrev Handle := Unit

instance : BEmit (String × Handle) Chunk' Char where
  take1 bh := match bh with
  | (b, h) => match String.length b with
    | 0 => (Chunk'.nil, b, h)
    | 1 => (Chunk'.fin (AB.a2b b), "", h)
    | _otherwise =>
      (Chunk'.cont (AB.a2b b), b.drop 1, h)

class MutCoe (x : Type u) (y : outParam (Type u)) where
  coe : x → y
  mutate : x → y → x

-- def takeN {f : Type u → Type u} {℘ ⅌ : Type u}
--           (src : s) (n : Nat)
--           [MutCoe s ℘] [Cont f ℘] [BEmit m s f β]
