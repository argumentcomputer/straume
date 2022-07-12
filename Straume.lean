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
For more details on this approach, consult this exchange in haskell-cafe:

> > On Mar 31, 2016 10:10 AM, "David Turner" < redacted >
> wrote:
> >>
> >> Hi Jonn,
> >>
> >> I work on a similar-sounding system. We have arranged things so that
> each node is a pure state machine, with outputs that are a pure function of
> its inputs, with separate (and simple, obviously correct) machinery for
> connecting these state machines over the network. This makes it rather
> simple to run a bunch of these state machines in a test harness that
> simulates all sorts of network nastiness (disconnections, dropped or
> reordered messages, delays, corruption etc.) on a single thread.
> >>
> >> One trick that proved useful was to feed in the current time as an
> explicit input message. This makes it possible to test things like timeouts
> without having to actually wait for the time to pass, which speeds things
> up immensely. We also make use of ContT somewhere in the tests to
> interleave processing and assertions, and to define a 'hypothetically'
> operator that lets a test run a sequence of actions and then backtrack.
> >>
> >> I think this idea was inspired by
> https://github.com/NicolasT/paxos/blob/master/bin/synod.hs, at least the
> network nastiness simulator thing. He uses threads for that demo but the
> nodes' behaviour itself is pure:
> https://github.com/NicolasT/paxos/blob/master/src/Network/Paxos/Synod/Proposer.hs
> for example.
> >>
> >> We also have proved certain key properties of the network are implied
> by certain local invariants, which reduces the testing problem down to one
> of checking properties on each node separately. This was time consuming,
> but highlighted certain important corner cases that it's unlikely we would
> have found by random testing.
> >>
> >> If you're interested in Byzantine behaviour (the 'evil node' test) then
> you may enjoy reading James Mickens' article on the subject:
> https://www.usenix.org/publications/login-logout/may-2013/saddest-moment
> >>
> >> Hope that helps,
> >>
> >> David
> >>
> >> On 31 March 2016 at 00:41, Jonn Mostovoy < redacted > wrote:
> >>>
> >>> Dear friends,
> >>>
> >>> we have a distributed system written in Haskell, consisting of three
> >>> types of nodes with dozen of instances of each of two types and a
> >>> central node of the third type.
> >>>
> >>> Each node is started by executing a binary which sets up acid-state
> >>> persistence layer and sockets over which msgpack messages are sent
> >>> around.
> >>>
> >>> It is trivial to write low level functionality quickcheck test suites,
> >>> which test properties of functions.
> >>>
> >>> We would like, however, to have a quickcheck-esque suite which sets up
> >>> the network, then gets it to an arbitrary valid state (sending correct
> >>> messages between nodes), then rigorously testing it for three
> >>> high-level properties:
> >>>
> >>> 1. Chaos monkey test (disable random node, see if certain invariants
> hold);
> >>> 2. Evil node test (make several nodes work against the system, see if
> >>> certain properties hold);
> >>> 3. Rigorous testing of network-wide invariants, if all the nodes
> >>> operate correctly.
> >>>
> >>> The problem we're facing is the following — if we want to inspect
> >>> state of nodes in Haskell-land, we have to write a huge machinery
> >>> which emulates every launch of node via thread. There will be bugs in
> >>> this machinery, so we won't be able to get quality testing information
> >>> before we fix those; if we want to run things as processes, then the
> >>> best thing we can do is to inspect either acid-state dbs of each node
> >>> (it poses resource locking problems and forces us to dump the state on
> >>> every change, which is undesirable), or make an observer node, which
> >>> dumps the consensus as Text and then parsing the data into Haskell
> >>> terms, making decisions about the required properties based on that
> >>> (so far, it feels like the best option).
> >>>
> >>> Am I missing something? How is something like this achieved in
> >>> culture? How would you approach such a problem?
> >>>
> >>> Links to source files of test suites which do something similar are
> >>> highly appreciated.
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


class Time (m : Type u → Type v) (σ : Type k) (T : Type u) (δ : Type u) [Inhabited σ] [Monad m] where
  τ : σ → m T
  Δτ : T → T → δ
  Δn (x₀ : T) : m δ :=
    τ default >>=
      fun x₁ => pure $ Δτ x₀ x₁

-- structure TimeS (m : Type u → Type v)
--                 (σ : Type k)
--                 (T : Type u)
--                 (δ : Type u)
--                 [Inhabited σ]
--                 [Monad m]
--                 [it : Time m σ T δ] where
--   τ : σ → m T := it.τ
--   Δτ : T → T → δ := it.Δτ
--   Δn (x₀ : T) : m δ :=
--     τ default >>=
--       fun x₁ => pure $ Δτ x₀ x₁

-- structure ThreeTypesInAStructSayNothingOfAMonad (s : Type) (t : Type → Type t) (a : Type) (b : Type) where
--   f : s → t a
--   g : a → a → b
--   ψ : a → t b
--   typeof_s := s
--   typeof_t := t
--   typeof_a := a
--   typeof_b := b

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
-/
structure Chunk (α : Type u) where
  data : α × Option Terminator

-- class Stream (a : Type uₐ) (mₐ : Type uₐ → Type vₐ)
--              (σₜ : Type uₜ) (mₜ : Type uₜ → Type vₜ) [Inhabited σₜ] [Monad mₜ] [Time mₜ σₜ T δₜ]
--              (αₖ : Type uₖ) [BEq αₖ] [PartialPOrdering αₖ] [Clock αₖ]
--              (buf : Nat := 2048)
--              (αₖ2 := Wristwatch) [BEq αₖ2] [PartialPOrdering αₖ2] [Clock αₖ2]
--              (αₖ3 := Wristwatch) [BEq αₖ3] [PartialPOrdering αₖ3] [Clock αₖ3]
--              where
--   /- "Give me a stream and a natural, and I'll produce two streams: a finite one with the desired amount of chunks, and the rest. " -/
--   splitAt (stream : mₐ a) (n : Nat := buf) : mₐ a × mₐ a
--   buffer := splitAt

universe u
universe v

/-
Simplest *practical* stream! It has strictly one source, hecnce the name.

✅ We are aware of the risks of using named instances.

But the alternative would be this:

```
  τ {mₜ : Type uₜ → Type uᵥ} : σ → mₜ T
  Δτ : T → T → δ
```

But then, how would lean understand that T is T? 🙅

This structure is really stupid. It doesn't know it's a stream. All the stuff happens in the functions like `splitAt`.
Note that they are generic in the wrapper-monad and in a particular time implementation.
So you can test everything under simulation outside IO.
-/
structure Uni (m : Type u → Type v) (a : Type u) where
  timestamp : (mₜ : Type p → Type q) → σ → mₜ T
  pos : Pos
  buf : Nat := 2048

-- timestamp := fun (it : Time s t a b) => it.τ

#check Uni.mk

abbrev Uni! m a := Uni m (Chunk a)
abbrev Uni? m a := Uni m $ Option (Chunk a)

def arrN (s : Uni! m a) (n : Nat := s.buf) : m (Array (Chunk a) × (Uni? m a)) := sorry
def arrWhile (s : Uni! m a) (P : Chunk a → Bool) : m ((Uni? m a) × (Uni? m a)) := sorry

-- TODO: Unwrap Array
def takeN (s : Uni! m a) := arrN s
def take1 (x : Uni! m a) := arrN x 1

def unUni (s : Uni! m a) : m (Chunk a) := sorry

#check IO.getStdin
#check FS.Stream

/-
Some cool functions for a cooler day. It's too hot today.
-/
-- def splitAt (s : Uni! m a) (n : Nat := s.buf) : m ((Uni! m a) × (Uni? m a)) := sorry
-- def span (s : Uni! m a) (P : Chunk a → Bool) : m ((Uni? m a) × (Uni? m a)) := sorry

-- def listN (s : Uni! m a) (n : Nat := s.buf) : m (List (Chunk a) × (Uni? m a)) := sorry
-- def listWhile (s : Uni! m a) (P : Chunk a → Bool) : m ((Uni? m a) × (Uni? m a)) := sorry
