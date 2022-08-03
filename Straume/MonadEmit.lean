namespace Straume.MonadEmit

class MonadEmit (m : Type u → Type v) (source : Type u) (value : Type u) where
  askFrom : source → Nat → m (value × source)

export MonadEmit (askFrom)

instance : MonadEmit IO IO.FS.Handle ByteArray where
  askFrom (src : IO.FS.Handle) (n : Nat) := do
    let bs ← IO.FS.Handle.read src (USize.ofNat n)
    return (bs, src)

instance : MonadEmit IO IO.FS.Handle String where
  askFrom src n := do
    let bah ← MonadEmit.askFrom src n
    return (String.fromUTF8Unchecked bah.1, bah.2)

def readStringNUnchecked
  (h : IO.FS.Handle) (n : Nat) : IO (String × IO.FS.Handle) :=
  MonadEmit.askFrom h n
