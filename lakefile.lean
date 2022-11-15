import Lake
open Lake DSL

package Straume

lean_lib Straume

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "adaa6c339d116c5fb67d924f0952c63603f2859b"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "89798a6cb76b2b29469ff752af2fd8543b3a5515"

@[default_target]
lean_exe straume {
  supportInterpreter := true
  root := "Main"
}

lean_exe Tests.Iterator
lean_exe Tests.Zeptoparsec
