import Lake
open Lake DSL

package Straume

@[defaultTarget]
lean_exe straume {
  supportInterpreter := true
  root := "Main"
}
