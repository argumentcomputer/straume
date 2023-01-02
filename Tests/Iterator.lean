import LSpec

import Straume.Iterator

open LSpec
open Straume.Iterator

def str : Iterator String := iter "This is a test string of 39 characters."
def bits : Iterator (List Bit) := iter $ Bit.listPad 10 $ Nat.toBits 43
def emptyBA : Iterator ByteArray := iter default

-- A helper function to turn any `Iterator` to `List` and back again,
-- allowing to do some manipulation on that `List` on the way.
private def lrt
  (s : α) (f : List β → List β) [Iterable α β] [Inhabited α] : α :=
    fromList $ f $ toList s

def listsTest :=
  let rtstr := "There and back again"
  let rtba := List.toByteArray [42, 10, 3]
  let rtbits := Nat.toBits 10
  group "toList/fromList roundtrip" $
    test "strings" (fromList (toList rtstr) = rtstr) $
    test "bytearray" (fromList (toList rtba) = rtba) $
    test "bits" (fromList (toList rtbits) = rtbits)

def extractTest
  (tdesc : String) (it : Iterator α)
    [Iterable α β] [Inhabited α] [DecidableEq α] : TestSeq :=
  group s!"{tdesc}, extracting" $
    test "0↔0: empty" (extract it it = default) $
    test "0↔4: four symbols"
      (extract it { it with i := 4 } = lrt it.s (List.take 4)) $
    test "4↔8: four symbols"
      (extract { it with i := 4 } { it with i := 8 } =
        lrt it.s (List.take 4 ∘ List.drop 4)) $
    test "0↔n, n > size: returns the whole string" $
      extract it {it with i := 100} = it.s

def forwardTest
  (tdesc : String) (it : Iterator α) [Iterable α β]
    [DecidableEq α] [DecidableEq β] [Inhabited α] [Inhabited β] : TestSeq :=
  let last := if it.s = default then default else (toList it.s).getLast!
  group s!"{tdesc}, forwarding" $
    test "no forwards past the edge"
      (curr (forward it 100) = last) $
    test "manual going past the edge returns last char" $
      curr ({ it with i := 100 }) = last

def emptyTest
  (tdesc : String) (it : Iterator α)
    [Iterable α β] [DecidableEq β] [Inhabited β] : TestSeq :=
  group s!"{tdesc}, empty" $
    test "no hasNext on empty iterator" (hasNext it = false) $
    test "current elem of empty iterator = default" $
      curr it = default

def main := lspecIO $
  listsTest ++

  extractTest "String" str ++
  extractTest "List Bit" bits ++

  forwardTest "String" str ++
  forwardTest "List Bit" str ++

  group "hasNext when only one element" (
    test "String" (hasNext $ iter ".") $
    test "List Bit" (hasNext $ iter [Bit.one]) $
    test "ByteArray" (hasNext $ iter $ List.toByteArray [42])) ++

  emptyTest "String" (iter "") ++
  emptyTest "List Bit" ((iter []) : Iterator (List Bit)) ++
  emptyTest "ByteArray" emptyBA
