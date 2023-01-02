import Lake
open Lake DSL

package Straume

lean_lib Straume

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "818538aced05fe563ef95bb3dcdf5ed755896139"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "129fd4ba76d5cb9abf271dc29208a28f45fd981e"

@[default_target]
lean_exe straume where
  root := `Main

lean_exe Tests.Iterator
lean_exe Tests.Zeptoparsec
