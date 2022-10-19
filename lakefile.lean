import Lake
open Lake DSL

package Straume

lean_lib Straume

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "876d29cb6f8011119a74712de7cb86280e408e3b"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "9c9f3cc9f3148c1b2d6071a35e54e4c5392373b7"

@[defaultTarget]
lean_exe straume {
  supportInterpreter := true
  root := "Main"
}

lean_exe Tests.Iterator
lean_exe Tests.Zeptoparsec
