import Init.System.IO
import Straume.Zeptoparsec

namespace Straume
/-
     The big idea of this library

      boxed stuff is implemented

 ┌───────┐
 │  Real │             ┌───────┐
 │ World ├─Driver─┬──► │Stream*|
 └───────┘        │    └───────┘
                  │
                  │
                  └──►  Async Stream

*- Stream exposes a synchronous interface for the asynchronous backend.


           ┌──────┐
   ┌───────┤Stream├─────────┐
   │       └───┬──┘         │
   │           │            │
   │           │            │
   │           │            │
   ▼           ▼            ▼
┌──────┐
│ Pull │     Sample        Push
│(file)│    (sensor)     (channel)
└──────┘



Every stream is laggy, samples are expected to fail, pushes are expected to be slow to present new data, if no new data has arrived yet.
Thus, every stream is equipped with a clock, as well as tracking how much data was streamed through it to the moment.
Reading from a stream implies a timeout.
It means that synchronous Stream (the only one currently implemented) is, really, a synchronous API for an async IO task.
Any read can fail with a timeout.

You can model a stream outside IO, say, for model checking and other testing approaches.
Code using Streams is be compatible with system testing if and only if the it is equpped with a facility to hoist the outer monad.

-/

/- False positives are used to represent probabilistic results.

TODO: It's known that the runtime we're targetting at Yatima isn't well-suited for Floats. Our ProbParOrd wants Float probabilities.
Perhaps, it makes sense, for probabilistic computations, to equip those with a probability approximation facilities to convert those to some close rational number.
class ToRational.

 -/
inductive FalsePositive where
| perhaps : Float → FalsePositive
| no
  deriving Repr, BEq

/- False negatives aren't currently used and are defined just for symmetry. -/
inductive FalseNegative where
| yes
| hardly : Float → FalseNegative
  deriving Repr, BEq

def forSure (x : Bool := true) : FalsePositive := if x then .perhaps 1.0 else .no
def surelyNot (x : Bool := true) : FalseNegative := if x then .hardly 1.0 else .yes

def anti (f : α → α → α) [BEq α] : α → α → α :=
  fun x y =>
    let z := f x y
    if z == x then y else x

/- Kind of like or, keeping the false positive with higher confidence. -/
def assure (x : FalsePositive) (y : FalsePositive) : FalsePositive :=
  match (x, y) with
  | (.perhaps xₙ, .no) => x
  | (.perhaps xₙ, .perhaps yₙ) => if (xₙ > yₙ) then x else y
  | (_, _) => y

/- Kind of like and, keeping the false positive with the lower confidence. -/
def doubt := anti assure

/- Kind of like and, keeping the false negative with higher confidence. -/
def disprove (x : FalseNegative) (y : FalseNegative) : FalseNegative :=
  match (x, y) with
  | (.hardly xₙ, .yes) => x
  | (.hardly xₙ, .hardly yₙ) => if (xₙ > yₙ) then x else y
  | (_, _) => y

/- Kind of like or, keeping the false positive with the highest confidence. -/
def convince := anti disprove

structure Incomparable

inductive POrdering where
| incomparable
| eq -- We use eq from BEq, so it's always certain
| lt : FalsePositive → POrdering
| gt : FalsePositive → POrdering

/-
Partial probabilistic ordering for timestamped events.
The probabilistic bit is needed for the forward compatibility with Bloom Clocks.

NB!
The wording is important.
Partial probabilistic ordering means that it's certainly partial and perhaps ordered.
If something is incomparable, you can be sure that the preimages of it are incomparable, if something is less than something else, you are given a confidence in the ordering.
-/
class PartialPOrdering (α : Type u) [BEq α] where
  lt : α → α → PSum Incomparable FalsePositive
  le : α → α → PSum Incomparable FalsePositive :=
    fun x y => match lt x y with
               | .inl _ => PSum.inl Incomparable.mk
               | .inr z => PSum.inr $ assure z (forSure $ BEq.beq x y)
  compare : α → α → POrdering :=
    fun x y => match le x y with
               | .inl _ => POrdering.incomparable
               | .inr .no => match le y x with
                             | .inl _ => POrdering.incomparable
                             | .inr .no => POrdering.eq
                             | .inr z => POrdering.gt z
               | .inr z => POrdering.lt z

-- TODO: add theorems? Extend PartialOrder from mathlib? Idk.

instance ord2pord [BEq α] [Ord α] : PartialPOrdering α where
  lt x y := .inr $ forSure $ Ordering.lt == Ord.compare x y

-- TODO: Namespace Straume.Clock.Logical

/-
A logical clock is something that can tick. Two clocks can merge into one.
-/
class Clock (α : Type u) [BEq α] [PartialPOrdering α] where
  tick : α → α
  merge : α → α → α

/-
The simplest logical clock.
-/
structure Wristwatch where
  face : Nat
  deriving Repr, BEq, Ord

instance instPPOrderingWristwatch : PartialPOrdering Wristwatch := ord2pord

instance instClockWristwatch : Clock Wristwatch where
  tick x := Wristwatch.mk $ 1 + x.face
  merge x y := Wristwatch.mk $ 1 + max x.face y.face

/-
Position counter in a stream is a clock such that every tick advances the universal time, thus merging adds.
-/
structure Pos where
  x : Nat
  deriving Repr, BEq, Ord

instance instPPOrderingGodswatch : PartialPOrdering Pos := ord2pord
instance instClockGodswatch : Clock Pos where
  tick p := Pos.mk $ 1 + p.x
  merge p q := Pos.mk $ p.x + q.x

/-
Four types m, σ, T, δ form a system of physical time if:
 * a timestamp T can be produced from state σ into monad m,
 * a distance δ can be calculated between two timestamps T,
 * a distance δ between some starting timestamp T and current time, returned in monad m.
-/
class Time (m : Type u → Type v) (σ : Type k) (T : Type u) (δ : Type u) [Inhabited σ] [Monad m] where
  τ : σ → m T
  Δτ : T → T → δ
  Δn (x₀ : T) : m δ :=
    τ default >>=
      fun x₁ => pure $ Δτ x₀ x₁

structure MSec where
  qty : Nat
  deriving Repr, BEq, Ord, Inhabited

structure NSec where
  qty : Nat
  deriving Repr, BEq, Ord, Inhabited

open IO

instance : Time BaseIO Unit MSec MSec where
  τ _ := MSec.mk <$> IO.monoMsNow
  Δτ x₀ x₁ := MSec.mk $ x₁.qty - x₀.qty

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

Suppose we have a variable length binary protocol such that the message length is encoded as a three bit integer.

 |-3-|----n----|-3-|---|
 | 7 | 1001111 | 1 | 0 |

Naturally, chunks are:

 1001111, .none

 001, .some eos

and are of type `Chunk (List Bit)`.

But if we insist, we consume it bit by bit by typing it as `Chunk Bit`:

 | 111 1001111 011 001 |

Chunks are

 1, .none
 1, .none
 1, .none
 1, .none
 0, .none
 ...
 1, .some eos

I hope it's clear. 🙇

TODO: rewrite this comment because now the type is an inductive!
-/
inductive Chunk (α : Type u) where
| nil
| cont : α → Chunk α
| fin : α × Option Terminator → Chunk α

/-
Simplest *practical* stream! It has strictly one source, hecnce the name.

This structure is really stupid. It doesn't know it's a stream. All the stuff happens in the functions like `splitAt`.
Note that they are generic in the wrapper-monad and in a particular time implementation.
So you can test everything under simulation outside IO.

The four-letter mnemonic for Uni is "MSRT": https://en.wikipedia.org/wiki/Deployable_Operations_Group#Maritime_Security_Response_Team_(MSRT): Monad-Source-Raw-Target.
-/
structure Uni (m : Type u → Type v) (h : Type u) (raw : Type u) (target : Type u) where
  ----------------------------------
  consume : m h → Nat → m (raw × h)
  bundle : raw → target
  ----------------------------------
  current : target
  source : h
  ----------------------------------
  timestamp (mₜ : Type p → Type q) (σ T : Type p) : σ → mₜ T
  pos : Pos
  buf : Nat := 64

#check Uni.mk

abbrev UniC m s r t := Uni m s r (Chunk t)

#check System.FilePath.mk

class MonadEmit (m : Type u → Type v) (source : Type u) (rawValue : Type u) where
  askFrom : m source → Nat → m (rawValue × source)

instance : MonadEmit IO IO.FS.Handle ByteArray where
  askFrom (src : IO IO.FS.Handle) (n : Nat) := do
    let handler <- src
    let bs <- IO.FS.Handle.read handler (USize.ofNat n)
    return (bs, handler)

def takeN (stream : UniC m s r t) (n : Nat) [Monad m] [MonadEmit m s r] : m (Array (Chunk a) × (UniC m s r t)) := do
    -- [:n].forIn Array.empty (fun _ acc => do
    --   sorry
    -- )
    return (Array.empty, stream)
  -- let (value, src₁) ←
-- TODO: Unwrapp Array
def take1 (stream : UniC m s r t) [Monad m] [MonadEmit m s r] : m (Array (Chunk a) × (UniC m s r t)) := takeN stream 1
def takeWhile (stream : UniC m s r t) [Monad m] [MonadEmit m s r] (P : Chunk a → Bool) : m ((UniC m s r t) × (UniC m s r t)) := sorry

#check IO.getStdin
#check FS.Stream

/-
TODO
-/
-- def splitAt (s : Uni! m a) (n : Nat := s.buf) : m ((Uni! m a) × (Uni? m a)) := sorry
-- def span (s : Uni! m a) (P : Chunk a → Bool) : m ((Uni? m a) × (Uni? m a)) := sorry

-- def listN (s : Uni! m a) (n : Nat := s.buf) : m (List (Chunk a) × (Uni? m a)) := sorry
-- def listWhile (s : Uni! m a) (P : Chunk a → Bool) : m ((Uni? m a) × (Uni? m a)) := sorry
