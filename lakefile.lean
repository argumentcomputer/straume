import Lake
open Lake DSL

package Straume

lean_lib Straume

require std from git
  "https://github.com/leanprover/std4" @ "v4.4.0"

require LSpec from git
  "https://github.com/lurk-lab/LSpec" @ "3388be5a1d1390594a74ec469fd54a5d84ff6114"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "3037f0c14128751b95510c2723f067ec7a494f08"

@[default_target]
lean_exe straume where
  root := `Main

lean_exe Tests.Iterator
lean_exe Tests.Zeptoparsec
