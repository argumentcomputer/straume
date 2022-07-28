namespace Straume.MonadEmit

class MonadEmit (m : Type u → Type v) (source : Type u) (value : Type u) where
  askFrom : m source → Nat → m (value × source)

export MonadEmit (askFrom)

instance : MonadEmit IO IO.FS.Handle ByteArray where
  askFrom (src : IO IO.FS.Handle) (n : Nat) := do
    let handler ← src
    let bs ← IO.FS.Handle.read handler (USize.ofNat n)
    return (bs, handler)
