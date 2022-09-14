import Lake
open Lake DSL

package Straume

lean_lib Straume

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "7e2d41644519e8c437fbe7461544eaa855738f73"

@[defaultTarget]
lean_exe straume {
  supportInterpreter := true
  root := "Main"
}

lean_exe Tests.Iterator
lean_exe Tests.Zeptoparsec
