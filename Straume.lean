import Straume.Zeptoparsec
import Straume.Chunk
import Straume.Buffer
import Straume.Clock
import Straume.Uni
import Straume.Clock
import Straume.Prob.Ordering

universe u
universe v

namespace Straume

structure Pos where
  i : Nat
  deriving DecidableEq, Repr, BEq, Ord

instance : HAdd Pos Pos Pos where
  hAdd x y := ⟨ x.i + y.i ⟩

class MonadEmit (m : Type u → Type v) (source : Type u) (value : Type u) where
  askFrom : m source → Nat → m (source × value)

instance : MonadEmit IO IO.FS.Handle ByteArray where
  askFrom (src : IO IO.FS.Handle) (n : Nat) := do
    let handler ← src
    let bs ← IO.FS.Handle.read handler (USize.ofNat n)
    return (handler, bs)
