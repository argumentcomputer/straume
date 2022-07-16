import Straume.Zeptoparsec

/- Chunks bundle Stream data into objects. The benchmark for the good UX for
those is for them to be parsable entirely with a Megaparsec. -/
namespace Chunk

/-
A way to terminate a stream.
`eos` means "end of stream", expected one.
`timeout` means that the Lean runner itself timed out (note that ioerr has `timeExpired` constructor, which is the same, but for OS timeouts)
`ioerr` means that we were running the stream as an IO task, and we got an IO error while performing it.

TODO: do we want to let the user control max chunk size and error out if it's too big?
-/
inductive Terminator where
| eos
| timeout
| ioerr : IO.Error → Terminator

/-
Suppose we have a variable length binary protocol such that the message length
is encoded as a three bit integer.

 |-3-|----n----|-3-|---|
 | 7 | 1001111 | 1 | 0 |

Naturally, chunks are:
 .cont [1,0,0,1,1,1,1],
 .fin [0,0,1], .eos

and are of type `Chunk Bit (List Bit)`.

But if we insist, we consume it bit by bit by typing it as `Chunk Bit Bit`:
 | 111 1001111 011 001 |
Chunks are
 .cont 1
 .cont 1
 .cont 1
 .cont 1
 .cont 0
 ...
 .fin 1, eos

I hope it's clear. 🙇
-/
inductive Chunk (α : Type u) where
| nil
| cont : α → Chunk α
| fin : α × Terminator → Chunk α