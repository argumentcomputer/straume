import Lake
open Lake DSL

package Straume

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "77fc51697abeff937ffd20d2050723dc0fa1c8c0"

@[defaultTarget]
lean_exe straume {
  supportInterpreter := true
  root := "Main"
}

lean_exe Tests.Iterator
lean_exe Tests.Zeptoparsec