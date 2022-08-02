import Straume
import Straume.Avots
import Straume.Chunk

open Straume.Chunk in
open Straume.Avots in
def main : IO Unit := do
  IO.println "STREAM DEMO 4! Now in 3D!"
  let file := System.mkFilePath [".", "Straume.lean"]
  let (zoink, _) ←
    IO.FS.withFile file (.read)
                   (fun handle => Straume.MonadEmit.askFrom handle 35)
  IO.println s!"{String.fromUTF8Unchecked zoink}"
  let (zoink1 : (Chunk String × (String × IO.FS.Handle))) ←
    IO.FS.withFile file (.read)
                   (fun handle =>
                      ((takeN (pure ("", handle) : IO (String × IO.FS.Handle)) (55 : Nat)) : IO (Chunk String × (String × IO.FS.Handle))))
