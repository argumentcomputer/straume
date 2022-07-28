import LSpec
import Straume.Iterator
import Straume.Zeptoparsec
import Straume.Bit

open Iterator
open Zeptoparsec
open ParseResult

def isSuccess : ParseResult α β → Bool
  | success _ _ => true
  | error _ _ => false

def const : α → β → α
  | a, _ => a

-- String parser tests

def srcStr : Iterator String := iter "This is a test string of 39 characters."

-- This is a general, non-string-specific test, but we place it here to
-- use the iterator and still have the rest of the tests semi-organized
def monadTest : TestSeq :=
  let t := Zeptoparsec.pure 'T' $ next srcStr
  test "Zeptoparsec.pure works" (anyChar srcStr = t) $
  test "Zeptoparsec.bind works" $
    (pstring "T" >>= const (return 'T')) srcStr = t

#lspec monadTest

def someCharsTest : TestSeq :=
  let pRes := someChars anyChar 4 srcStr
  test "someChars parses successfully" (isSuccess pRes) $ match pRes with
    | success pos res =>
      test s!"First 4 chars of '{srcStr.s}' is 'This'" ("This" = res) $
      test "Iterator now points to position 4" (4 = pos.i)
    | error _ _ => test "Unreachable" false

#lspec someCharsTest

def asciiTest : TestSeq :=
  let expectedPrefix := "This is a test string of "
  let expected := Zeptoparsec.pure expectedPrefix $ forward srcStr 25
  let letterOrSpace := orElse asciiLetter (fun _ => pchar ' ')
  let afterLetters := manyChars letterOrSpace srcStr
  test "Letter OR space prefix" (expected = afterLetters) $
  test "Next 2 chars are digits" $
    many1Chars digit (deparse afterLetters) =
    someChars anyChar 2 (deparse expected)

#lspec asciiTest

-- ByteArray parser tests

-- List Bit parser tests

open Bit

def srcBits : Iterator (List Bit) := iter $ pad 10 $ natToBits 43

def manyRepsTest : TestSeq :=
  test "We can parse out groups of max 3 bits" $
    isSuccess $ many (someChars anyChar 3) srcBits

#lspec manyRepsTest

def main : IO UInt32 := do
  let _ ← lspec monadTest
  let _ ← lspec someCharsTest
  let _ ← lspec asciiTest
  lspec manyRepsTest