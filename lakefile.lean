import Lake
open Lake DSL

package Straume

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "3b759f6e7798fdb6b17ae83ea060cd34e89b7e91"

@[defaultTarget]
lean_exe straume {
  supportInterpreter := true
  root := "Main"
}

-- Tests

lean_exe Tests.Zeptoparsec
