import Lake
open Lake DSL

package Straume

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "3b759f6e7798fdb6b17ae83ea060cd34e89b7e91"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "8f609e0ed826dde127c8bc322cb6f91c5369d37a"

@[defaultTarget]
lean_exe straume {
  supportInterpreter := true
  root := "Main"
}

lean_exe Tests.Zeptoparsec