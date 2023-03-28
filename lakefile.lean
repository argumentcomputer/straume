import Lake
open Lake DSL

package Straume

lean_lib Straume

require LSpec from git
  "https://github.com/lurk-lab/LSpec" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "f549e2a841b0641b9385ecf41a270142b7ae506a"

@[default_target]
lean_exe straume where
  root := `Main

lean_exe Tests.Iterator
lean_exe Tests.Zeptoparsec
