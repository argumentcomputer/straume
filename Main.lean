import Straume

open Straume.Chunk in
open Straume in
open Zeptoparsec in
open Straume.Iterator in

def main : IO Unit := do
  IO.println "STREAM DEMO 9000! NOW WORKING!"
  let file := System.mkFilePath ["./Tests/", "PrideAndPrejudice.txt"]

  IO.println "Let's read some Jane Austin!\n"
  let (zoink, h₀) ← IO.FS.withFile file (.read)
    (fun handle => Straume.MonadEmit.askFrom handle 38)
  IO.println s!"{String.fromUTF8Unchecked zoink}\n"

  IO.println "Nice! How does that sentence end? Let's find out, with CHUNKS!\n"
  let ((zoink1 : Chunk String), (buff₁, h₁)) ← takeN 80 ("", h₀) 200
  IO.println s!"CHUNK IS {zoink1}"
  IO.println s!"BUFFER IS {buff₁}"

  IO.println "\nOh, it's a classic. Let's read the whole Chapter 1!\n"
  let ((zoink2 : Chunk String), (buff₂, _)) ← takeN 80000 ("", h₁)
  IO.println s!"CHUNK IS {zoink2}"
  IO.println s!"BUFFER IS {if buff₂ == "" then "EMPTY" else buff₂}"

  IO.println "\nVery cool. Let's go from the top UNTIL we find a PERIOD.\n"
  let ((zoink3 : Chunk String), _) ← IO.FS.withFile file (.read)
    (fun handle => takeWhile (fun c => c != '.') ("", handle))

  IO.println s!"CHUNK IS {zoink3}"
  IO.println s!"BTW, CHUNK'S SIZE IS {Aka.chunkLength zoink3}"

  -- Example of subsequent Zeptoparsec usage

  let sentencesP := attempt $ do
    let body ← manyChars (satisfy (fun c => c != '.'))
    _ ← pchar '.' *> optionalP ws
    pure $ body ++ "."

  let sentences :=
    match (Zeptoparsec.run (many sentencesP) $ coreturn zoink2) with
    | Except.ok res => res
    | Except.error _ => default

  let small := List.filter (fun s => s.length < 50) $ sentences.toList

  IO.println small.length
  IO.println small
