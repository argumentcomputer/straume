import Lake
open Lake DSL

package Straume

lean_lib Straume

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "515b7eff7765dcf55ce275ac41fa13a30a59f1d0"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "129fd4ba76d5cb9abf271dc29208a28f45fd981e"

@[default_target]
lean_exe straume where
  root := `Main

lean_exe Tests.Iterator
lean_exe Tests.Zeptoparsec
