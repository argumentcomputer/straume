structure RichStreamIterator (m : Type u → Type v) (h raw target : Type u) where
  consume : m h → Nat → m (raw × h)
  bundle : raw → target
  value : target

class Emit (m : Type u → Type v) (source raw : Type u) where
  consume : m source → Nat → m (raw × source)

instance : Emit IO IO.FS.Handle ByteArray where
  consume (src : IO IO.FS.Handle) (n : Nat) := do
    let handle <- src
    let bs <- IO.FS.Handle.read handle (USize.ofNat n)
    return (bs, handle)

abbrev RSI m s r t := RichStreamIterator m s r t

def takeN (x : RSI m s r t) (_n : Nat)
          [Emit m s r] [Monad m]
          : m (Array t × RSI m s r t) := do
  return (Array.empty, x)

def flipTakeN (n : Nat) (x : RSI m s r t)
              [Emit m s r] [Monad m]
              : m (Array t × RSI m s r t) := takeN x n

def take1 := flipTakeN 1