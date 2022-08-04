import Straume.MonadEmit

open Straume.MonadEmit (readStringN)

namespace Straume.Flood

/- A way to flood a buffer of some source `s` with more data. -/
class Flood (m : Type u → Type v)
            (s : Type u) where
  flood (_ctx : s) (_buffer : Nat := 2048) : m s

instance : Flood IO (String × IO.FS.Handle) where
  flood xh b := do
    let (x, h) := xh
    let (x₁, h₁) ← readStringN h b
    pure (String.append x x₁, h₁)
