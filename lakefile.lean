import Lake
open Lake DSL

package Straume

@[defaultTarget]
lean_exe straume {
  supportInterpreter := true
  root := "Main"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "8f609e0ed826dde127c8bc322cb6f91c5369d37a"
