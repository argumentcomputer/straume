import Straume

open Straume.Chunk in
open Straume.Aka in

def main : IO Unit := do
  IO.println "STREAM DEMO 9000! NOW WORKING!"
  let file := System.mkFilePath ["./Tests/", "PrideAndPrejudice.txt"]

  IO.println "Let's read some Jane Austin!\n"
  let (zoink, h₀) ← IO.FS.withFile file (.read)
    (fun handle => Straume.MonadEmit.askFrom handle 38)
  IO.println s!"{String.fromUTF8Unchecked zoink}\n"

  IO.println "Nice! How does that sentence end? Let's find out, with CHUNKS!\n"
  let ((zoink1 : Chunk String), (buff₁, h₁)) ← takeN ("", h₀) 80 200
  IO.println s!"CHUNK IS {zoink1}"
  IO.println s!"BUFFER IS {buff₁}"

  IO.println "\nOh, it's a classic. Let's read the whole Chapter 1!\n"
  let ((zoink2 : Chunk String), (buff₂, _)) ← takeN ("", h₁) 80000
  IO.println s!"CHUNK IS {zoink2}"
  IO.println s!"BUFFER IS {if buff₂ == "" then "EMPTY" else buff₂}"

  IO.println "\nVery cool. Let's go from the top UNTIL we find a PERIOD.\n"
  let ((zoink3 : Chunk String), _) ← IO.FS.withFile file (.read)
    (fun handle => takeWhile (fun c => c != '.') ("", handle))

  IO.println s!"CHUNK IS {zoink3}"
  IO.println s!"BTW, CHUNK'S SIZE IS {chunkLength zoink3}"
