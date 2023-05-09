import Lake
open Lake DSL

package Straume

lean_lib Straume

require std from git
  "https://github.com/leanprover/std4" @ "6006307d2ceb8743fea7e00ba0036af8654d0347"

require LSpec from git
  "https://github.com/lurk-lab/LSpec" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "974c288349a412aea92bb0780efc81fa5f79e442"

@[default_target]
lean_exe straume where
  root := `Main

lean_exe Tests.Iterator
lean_exe Tests.Zeptoparsec
