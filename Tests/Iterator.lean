import LSpec
import Straume.Bit
import Straume.Iterator

open LSpec
open Straume.Iterator
open Bit

def srcStr : Iterator String := iter "This is a test string of 39 characters."
def srcBits : Iterator (List Bit) := iter $ pad 10 $ natToBits 43

def extractTest :=
  test "Extracting 0↔0: empty" (extract srcStr srcStr = default) $
  test "Extracting 0↔4: four symbols"
    (extract srcStr { srcStr with i := 4 } = "This") $
  test "Extracting 4↔8: four symbols"
    (extract { srcStr with i := 4 } { srcStr with i := 8 } = " is ") $
  test "Extracting 0↔n, n > size: returns the whole string" $
    extract srcStr {srcStr with i := 100} = srcStr.s

def forwardTest :=
  test "No forwards past the edge" (curr (forward srcStr 100) = '.') $
  test "Manual going past the edge returns last char" $
    curr ({ srcStr with i := 100 }) = '.'

def main := lspecIO $
  extractTest ++
  forwardTest