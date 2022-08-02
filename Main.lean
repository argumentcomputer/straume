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
  IO.println "WHO LET THE CHUNK OUT? WHO? WHO? WHO?"
  let (zoink1 : (Chunk String × (String × IO.FS.Handle))) ←
    IO.FS.withFile file (.read)
                   (fun handle =>
                      takeN (pure ("", handle)) 55)
  IO.println s!"CHUNK IS {zoink1.1}"
  IO.println s!"BUFFER IS {zoink1.2.1}"
  IO.println "* * *"
  IO.println "* * *"
  IO.println "* * *"
  IO.println "Let's read it all"
  let ((zoink2 : (Chunk String)), (buff, _)) ←
    IO.FS.withFile file (.read)
                   (fun handle =>
                      takeN (pure ("", handle)) 1468)
  IO.println s!"CHUNK IS {zoink2}"
  IO.println s!"BUFFER IS {if buff == "" then "EMPTY" else buff}"
