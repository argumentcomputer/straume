import Straume

def askFrom : IO IO.FS.Handle → Nat → IO (IO.FS.Handle × ByteArray) :=
  Straume.instMonadEmitIOHandleByteArray.askFrom

def main : IO Unit := do
  IO.println "STARTING STREAM DEMO 2"
  let (zoink, _) <-
    IO.FS.withFile (System.mkFilePath [".", "Straume.lean"])
                   (.read)
                   (fun handle => askFrom (pure handle) 228)
  IO.println s!"{String.fromUTF8Unchecked zoink}"

#check IO.FS.withFile
#check Straume.MonadEmit.askFrom
